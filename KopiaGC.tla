------------------------------ MODULE KopiaGC ------------------------------
(*
    This is a spec to model behaviours of the interaction of Snapshot and GC processes in Kopia based on Julio's proposal of saving
    mark manifests and having a separate Repair & Discard phase.

    It is based out of my understanding of the code as of this commit in Julio's Kopia repo -
        https://github.com/julio-lopez/kopia/commit/132f823d4f1a321c88cdd5a4a880441800ef1c49

    General ideas followed while writing the spec are outlined at https://pkj415.github.io/TLA-Protocols/docs/kopia_gc_tla/

*)

\* TODO - A deleted content entry can get removed during small index compaction if the entry is older than SkipDeletedOlderThan

EXTENDS Integers, Sequences, FiniteSets, Bags, TLC

CONSTANT
    NumContents, \* Restrict behaviours to snapshots that can contain contents with content IDs 0..NumContents-1
    MaxSnapshotTime, \* Maximum number of logical time steps a snapshot process can take. Post that it will not be able to mark itself "completed".
    MaxLogicalTime, \* Can't keep TLC running forever
    MaxSnapshotProcessesIssued, \* Maximum number of snapshot processes that can be issued. Constraint needed to restrict state space, else TLC will run forever
    MaxGCMarksIssued, \* Maximum number of GC Mark processes that can be issued.
    MaxGCRepairDiscardsIssued, \* Maximum number of GC Repair & Discard processes that can be issued.
    MinGCMarkAge \* Only Mark phases with mark_phase.end_timestamp + MinGCMarkAge <= current_timestamp can be repaired.
    (* TODO - Explain how logical time is modeled, and how this field changes the scope of possible behaviours *)

ASSUME MinGCMarkAge >= MaxSnapshotTime \* MinGCMarkAge can only be >= MaxSnapshotTime. That is the protocol.

VARIABLES
        (* Format - Set of content info entries. Not having a bag will not affect safety verification because
            having more than one index entry with the same timestamp for the same content will eventually get merged into
            a single index entry. Also, safety wouldn't be affected in case we assume that the index compation process
            merges index entries without any entry vanishing temporarily (which we can reason from the protocol). So, in
            a nutshell, we are not considering a bag index entries and hence also ignoring the index compaction process.
            {
                [content_id |-> 0, deleted |-> TRUE/FALSE, timestamp |-> 0]
            }
        *)
        index_entries,

        (* Format - Bag of records.
            {
             [status |-> "in_progress", "completed", "deleted", \* "completed" is analogous to the manifest for the snapshot being written to the store. When we
                 refer to "snapshot" it means that the corresponding process had completed and it will be signified by this data structure with status as "completed".
              contents_written |-> Contents that have been written to the blob storage for the snapshot,
              index_entries |-> Point in time view of index_entries read at the start of snapshotting process, later this is updated on every
                flush of indices. Note that the update will only append flushed indices to this field. The indices are not refreshed from
                the global set index_entries.
              index_entries_to_be_flushed |-> new local index entries that can be flushed to global set index_entries,
              start_timestamp |-> start_timestamp]
            }
        *)
        snapshot_processes,

        (*
            {
                [
                    snapshots |-> Point in time view of the snapshots in the repository. Populated when this GC is triggered.
                    index_entries |-> Point in time view of the global set index_entries.
                    contents_deleted |-> set of deleted content ids,
                    next_mark_mainfest_start_time |-> -1, \* When a new batch of contents to be deleted is started, this is set.
                        It is reset to -1 when a batch of deletes is flushed with the corresponding Mark manifest.
                    deletions_to_be_flushed |-> index entries of deleted contents that can be flushed to global index_entries
                ]
            }
        *)
        gc_marks, \* TODO: Consider deleting gc_marks which have completed because they don't help in the decision of behaviours' path later. Just exploding the state space.

        (*
            {
                [
                    start_timestamp,
                    end_timestamp,
                    snapshots |-> snapshots seen,
                    deletes_flushed |-> content id deletes that were flushed
                ]
            }
        *)
        gc_mark_manifests,

        (*
            {
                [
                    snapshots |-> Point in time view of the snapshots in the repository,
                    mark_manifests |-> Set of mark manifests,
                    index_entries |-> Point in time view of the global set index_entries,
                    stage |-> "start"/ "repaired" / "populated_content_ids_to_discard",
                    content_ids_to_discard |-> {}
                ]
            }
        *)
        gc_repair_discards,
        current_timestamp

KopiaInit == /\ snapshot_processes = EmptyBag
             /\ current_timestamp = 0
             /\ index_entries = {}
             /\ gc_marks = EmptyBag
             /\ gc_mark_manifests = EmptyBag
             /\ gc_repair_discards = EmptyBag

NonEmptyPowerset(s) == (SUBSET s \ {{}})

IndexEntriesTypeOK == index_entries \in SUBSET(
                        [content_id: 0..NumContents-1,
                         deleted: {TRUE, FALSE},
                         timestamp: 0..MaxLogicalTime])

\* TODO: Add type checks for other state variables.
KopiaTypeOK == /\ IndexEntriesTypeOK
               /\ current_timestamp \in 0..MaxLogicalTime

(***************************************************************************
    Utilities related to index entries
 ***************************************************************************)
HasContentInfo(idx_entries, content_id) ==
    LET matching_content_infos == {
        content_info \in idx_entries: content_info.content_id = content_id}
    IN IF matching_content_infos # {} THEN TRUE
        ELSE FALSE

\* Call this only if HasContentInfo is TRUE.
GetContentInfo(idx_entries, content_id) ==
    LET matching_content_infos == {
            content_info \in idx_entries: content_info.content_id = content_id}
        max_timestamp == CHOOSE timestamp \in {content_info.timestamp: content_info \in matching_content_infos}:
                            \A content_info \in matching_content_infos: timestamp >= content_info.timestamp
        latest_matching_content_infos == {
            content_info \in matching_content_infos: content_info.timestamp = max_timestamp}
    IN IF \E content_info \in latest_matching_content_infos: content_info.deleted = FALSE
       THEN CHOOSE content_info \in latest_matching_content_infos: content_info.deleted = FALSE
       ELSE CHOOSE content_info \in latest_matching_content_infos: TRUE

\* Define set of all content IDs in the idx_entries set passed irrespective of whether they are deleted or not.
ContentIDs(idx_entries) == {content_info.content_id: content_info \in idx_entries}

\* MergeIndices is a simple union.
MergeIndices(idx_blobs_1, idx_blobs_2) == idx_blobs_1 \cup idx_blobs_2

(***************************************************************************
    Snapshot process steps
 ***************************************************************************)
WriteContents(snap) ==
   \E contents_to_write \in NonEmptyPowerset(0..NumContents-1 \ snap.contents_written):
       \* Pick only those contents which have not been written till now. Even if a snapshot has the same content multiple times
       \* it would only write it to the data blob storage the first time and also add to index_entries only once.
       LET contents_non_existing == {c_id \in contents_to_write:
             (\/ ~ HasContentInfo(snap.index_entries, c_id)
              \/ GetContentInfo(snap.index_entries, c_id).deleted)}
           content_info_entries == [content_id: contents_non_existing,
             timestamp: {current_timestamp},
             deleted: {FALSE}]
           updated_snapshot == [snap EXCEPT !.contents_written = snap.contents_written \cup contents_to_write,
                                            !.index_entries_to_be_flushed = snap.index_entries_to_be_flushed \cup content_info_entries]
       IN snapshot_processes' = (snapshot_processes (-) SetToBag({snap})) (+) SetToBag({updated_snapshot})
 
FlushNewIndexEntries(snapshot) ==
   LET
       updated_snapshot == [snapshot EXCEPT !.index_entries = MergeIndices(snapshot.index_entries, snapshot.index_entries_to_be_flushed),
                                            !.index_entries_to_be_flushed = {}]
   IN
       /\ snapshot_processes' = (snapshot_processes (-) SetToBag({snapshot})) (+) SetToBag({updated_snapshot})
       /\ index_entries' = MergeIndices(index_entries, snapshot.index_entries_to_be_flushed)

TriggerSnapshot ==
    snapshot_processes' = snapshot_processes (+) SetToBag({[
        status |-> "in_progress", contents_written |-> {},
        index_entries |-> index_entries,
        index_entries_to_be_flushed |-> {},
        start_timestamp |-> current_timestamp]})

SnapshotProcessing ==
  \/ \* Trigger a snapshot
    /\ BagCardinality(snapshot_processes) < MaxSnapshotProcessesIssued
    /\ TriggerSnapshot
    /\ UNCHANGED <<index_entries, current_timestamp, gc_marks, gc_mark_manifests, gc_repair_discards>>

  \/
    /\ \E snapshot \in BagToSet(snapshot_processes):
        \/  \* Write some contents to a blob
            /\ snapshot.status = "in_progress"
            /\ WriteContents(snapshot)
            /\ UNCHANGED <<index_entries, current_timestamp, gc_marks, gc_mark_manifests, gc_repair_discards>>
        
        \/  \* Flush new index_entries
            /\ snapshot.status = "in_progress"
            /\ snapshot.index_entries_to_be_flushed # {}
            /\ FlushNewIndexEntries(snapshot)
            /\ UNCHANGED <<current_timestamp, gc_marks, gc_mark_manifests, gc_repair_discards>>
        
        \/  \* Complete snapshot
            /\ snapshot.status = "in_progress"
            /\ current_timestamp < snapshot.start_timestamp + MaxSnapshotTime
            /\ snapshot.index_entries_to_be_flushed = {} \* There is nothing to be flushed
            /\ LET updated_snapshot == [snapshot EXCEPT !.status = "completed"]
               IN  /\ UNCHANGED <<index_entries, current_timestamp, gc_marks, gc_mark_manifests, gc_repair_discards>>
                   /\ snapshot_processes' = (snapshot_processes (+) SetToBag({updated_snapshot})) (-) SetToBag({snapshot})
        
        \/  \* Delete a snapshot
            /\ snapshot.status = "completed"
            /\ LET updated_snapshot == [snapshot EXCEPT !.status = "deleted"]
               IN  /\ snapshot_processes' = (snapshot_processes (+) SetToBag({updated_snapshot})) (-) SetToBag({snapshot})
                   /\ UNCHANGED <<index_entries, current_timestamp, gc_marks, gc_mark_manifests, gc_repair_discards>>
            \* TODO: Since nothing would be used post deletion, try to check if setting all other variables to default value helps in reducing state space.

(***************************************************************************
    Mark process steps
 ***************************************************************************)
UnusedContentIDs(idx_entries, snaps) == {content_id \in ContentIDs(idx_entries):
    /\ ~ GetContentInfo(idx_entries, content_id).deleted} \ UNION{snap.contents_written: snap \in snaps}

\* TriggerGC stores a point in time view of snapshots and the global set index_entries in the GC process record.
\* Consider only completed snapshot processes in TriggerGC, this helps in reducing state space. Reasoning - If all snapshot processes were kept in the GC process record,
\* two states with GC processes having the same set of completed snapshots but different set of non-completed snapshots would be differentiated,
\* even though the behaviour following those states won't be affected by the non-completed snapshots stored in the GC record (GC doesn't use the
\* information in non-completed records).

\* Consider only those index entries which are old enough. Do it in Trigger instead of having a check in UnusedContentIDs (to
\* reduce state space). Here MaxSnapshotTime acts analogous to minContentAge in actual code.
TriggerGCMark ==
    gc_marks' = gc_marks (+) SetToBag({[snapshots |-> {snap \in BagToSet(snapshot_processes): snap.status = "completed"},
        index_entries |-> {content_info \in index_entries: current_timestamp >= (content_info.timestamp + MaxSnapshotTime)},
        next_mark_mainfest_start_time |-> -1, \* Batch of contents to be deleted is not yet complete.
        contents_deleted |-> {},
        deletions_to_be_flushed |-> {}
       ]})

\* TODO - If content iteration is in some specific order, the state space can be reduced. Right now the specification allows
\* deletion in any order.
DeleteContents(gc_mark) ==
    \E content_ids_to_delete \in NonEmptyPowerset(UnusedContentIDs(gc_mark.index_entries, gc_mark.snapshots) \ gc_mark.contents_deleted):
        \* Earlier gc.contents_deleted was a set of contents and not content ids. That wasn't required and leads to a larger state space. TODO - Ponder on this.
        LET contents_to_delete == [content_id: content_ids_to_delete, timestamp: {current_timestamp}, deleted: {TRUE}]
            updated_gc_mark == [gc_mark EXCEPT !.contents_deleted = gc_mark.contents_deleted \cup {content.content_id: content \in contents_to_delete},
                                               !.deletions_to_be_flushed = gc_mark.deletions_to_be_flushed \cup contents_to_delete,
                                               !.next_mark_mainfest_start_time = IF gc_mark.next_mark_mainfest_start_time = -1 THEN current_timestamp
                                                                                 ELSE gc_mark.next_mark_mainfest_start_time]
        IN
            gc_marks' = (gc_marks (-) SetToBag({gc_mark})) (+) SetToBag({updated_gc_mark})

FlushDeletedContents(gc_mark) ==
    LET
        \* No need to update the gc_mark.index_entries like we did for snapshot processes. This is because once a content is deleted by its
        \* presence in gc_mark.contents_deleted, it will never be checked again in gc_mark.index_entries.
        updated_gc_mark == [gc_mark EXCEPT !.deletions_to_be_flushed = {},
                                           !.next_mark_mainfest_start_time = -1]
    IN
        /\ gc_marks' = (gc_marks (-) SetToBag({gc_mark})) (+) SetToBag({updated_gc_mark})
        /\ index_entries' = MergeIndices(index_entries, gc_mark.deletions_to_be_flushed)
        /\ gc_mark_manifests' = gc_mark_manifests (+) SetToBag({[start_timestamp |-> gc_mark.next_mark_mainfest_start_time,
               end_timestamp |-> current_timestamp,
               deletes_flushed |-> {deletion.content_id: deletion \in gc_mark.deletions_to_be_flushed},
               snapshots |-> gc_mark.snapshots]})

GC_Mark == \/
              \* Trigger GC Mark phase. Load index_entries and completed snapshot processes (not all, to save on state space) at the current_timestamp.
              /\ BagCardinality(gc_marks) < MaxGCMarksIssued
              /\ TriggerGCMark
              /\ UNCHANGED <<snapshot_processes, index_entries, current_timestamp, gc_mark_manifests, gc_repair_discards>>
           \/
              \* Delete some contents which are in index_entries, but not referenced by the snapshots.
              /\ \E gc_mark \in BagToSet(gc_marks):
                  /\ DeleteContents(gc_mark)
                  /\ UNCHANGED <<snapshot_processes, index_entries, current_timestamp, gc_mark_manifests, gc_repair_discards>>
           \/ \* Flush local index_entries of deleted contents along with a mark manifest
              /\ \E gc \in BagToSet(gc_marks):
                  /\ gc.deletions_to_be_flushed # {}
                  /\ FlushDeletedContents(gc)
                  /\ UNCHANGED <<snapshot_processes, current_timestamp, gc_repair_discards>>

(***************************************************************************
    Repair and Discard process steps
 ***************************************************************************)
TriggerGCRepairDiscard ==
    gc_repair_discards' = gc_repair_discards (+) SetToBag({[snapshots |-> {snap \in BagToSet(snapshot_processes): snap.status = "completed"},
        mark_manifests |-> {manifest \in BagToSet(gc_mark_manifests): current_timestamp >= (manifest.end_timestamp + MinGCMarkAge)},
        index_entries |-> index_entries,
        stage |-> "start",
        content_ids_to_discard |-> {}
       ]})

Repair(repair_discard) ==
    LET
        \* Set of snapshots which were not seen by the mark manifests.
        snapshots_to_check == UNION{repair_discard.snapshots \ manifest.snapshots: manifest \in repair_discard.mark_manifests}
        contents_to_maybe_repair == UNION{snapshot.contents_written: snapshot \in snapshots_to_check}
        contents_to_repair == {content_id \in contents_to_maybe_repair:
                                   /\ HasContentInfo(repair_discard.index_entries, content_id)
                                   /\ GetContentInfo(repair_discard.index_entries, content_id).deleted = TRUE}
        index_to_flush == [content_id: contents_to_repair, timestamp: {current_timestamp}, deleted: {FALSE}]
        updated_repair_discard == [repair_discard EXCEPT !.stage = "repaired"]
    IN
        /\ index_entries' = MergeIndices(index_entries, index_to_flush)
        /\ gc_repair_discards' = (gc_repair_discards (-) SetToBag({repair_discard})) (+) SetToBag({updated_repair_discard})

PopulateContentIDsToDiscard(repair_discard) ==
    LET
        marked_content_ids == UNION{manifest.deletes_flushed: manifest \in repair_discard.mark_manifests}
        content_ids_to_discard == {content_id \in marked_content_ids:
                                      /\ HasContentInfo(repair_discard.index_entries, content_id)
                                      /\ GetContentInfo(repair_discard.index_entries, content_id).deleted}
        updated_repair_discard == [repair_discard EXCEPT !.content_ids_to_discard = content_ids_to_discard,
                                                         !.stage = "populated_content_ids_to_discard"]
    IN
        gc_repair_discards' = (gc_repair_discards (-) SetToBag({repair_discard})) (+) SetToBag({updated_repair_discard})

Discard(repair_discard) ==
    LET
        all_contents_to_remove_from_global_index ==
            {content \in repair_discard.index_entries: content.content_id \in repair_discard.content_ids_to_discard}
    IN
        \E contents_to_remove_from_global_index \in NonEmptyPowerset(all_contents_to_remove_from_global_index):
            \* With this we are simulating deletions of chunks of contents in the indices. Contents might be
            \* discarded in any size of batches. In the actual systems, contents in the same index blob
            \* are discarded together (and many index blobs are deleted in sequence after the compacted index is written).
            \* In the actual system an index blob is deleted at once but with this random chunk deletion
            \* that we have done, we are allowing more behaviours than are allowed in actual i.e., we are also
            \* allowing behaviours with contents from different index blobs deleted together and also the case
            \* where contents to be discarded from the same index blob are not discarded together.
           /\ index_entries' = index_entries \ contents_to_remove_from_global_index
           /\ LET
                 updated_repair_discard == [repair_discard EXCEPT !.index_entries = repair_discard.index_entries \ contents_to_remove_from_global_index]
              IN
                 gc_repair_discards' = (gc_repair_discards (-) SetToBag({repair_discard})) (+) SetToBag({updated_repair_discard})

\*RemoveManifests(repair_discard) == LET
\*                                      all_contents_to_remove_from_global_index ==
\*                                        {content \in repair_discard.index: content.content_id \in repair_discard.content_ids_to_discard}
\*                                   IN
\*                                      /\ all_contents_to_remove_from_global_index = {} \* All contents to be discarded have been discarded. Now, delete the mark manifests.
\*                                      /\ gc_mark_manifests' = gc_mark_manifests (-) repair_discard.mark_manifests

GC_Repair_Discard ==
    \/
        \* Trigger GC Repair and Discard phase. Load the completed snapshot processes and mark manifests (older than the safety threshold mentioned earlier).
        /\ BagCardinality(gc_repair_discards) < MaxGCRepairDiscardsIssued
        /\ TriggerGCRepairDiscard
        /\ UNCHANGED <<snapshot_processes, index_entries, current_timestamp, gc_marks, gc_mark_manifests>>
    \/
        /\ \E repair_discard \in BagToSet(gc_repair_discards):
             \/ \* Repair contents
                /\ repair_discard.stage = "start"
                /\ Repair(repair_discard)
                /\ UNCHANGED <<snapshot_processes, current_timestamp, gc_marks, gc_mark_manifests>>
             \/ \* Populate content IDs to discard
                /\ repair_discard.stage = "repaired"
                /\ PopulateContentIDsToDiscard(repair_discard)
                /\ UNCHANGED <<snapshot_processes, current_timestamp, gc_marks, gc_mark_manifests, index_entries>>
             \/ \* Discard contents
                /\ repair_discard.stage = "populated_content_ids_to_discard"
                /\ Discard(repair_discard)
                /\ UNCHANGED <<snapshot_processes, current_timestamp, gc_marks, gc_mark_manifests>>
\*                             \/ \* Remove manifests if all contents to be removed in the discard phase have been removed
\*                                /\ repair_discard.stage = "populated_content_ids_to_discard"
\*                                /\ RemoveManifests(repair_discard)
\*                                /\ UNCHANGED <<snapshot_processes, current_timestamp, gc_marks, index_entries, gc_repair_discards>>

KopiaNext ==
    \/
        /\ SnapshotProcessing
    \/
        /\ GC_Mark
    \/
        /\ GC_Repair_Discard
    \/
        \* Tick time forward.
        /\ current_timestamp < MaxLogicalTime
        /\ current_timestamp' = current_timestamp + 1
        /\ UNCHANGED <<index_entries, snapshot_processes, gc_marks, gc_mark_manifests, gc_repair_discards>>

(* Invariants and safety check *)
GCInvariant ==
    \A snap \in {snap \in BagToSet(snapshot_processes): snap.status = "completed"}:
        /\ \A content_id \in snap.contents_written:
            /\ HasContentInfo(index_entries, content_id)

GetContentInfoCheck ==
    ~ \E content1, content2 \in index_entries:
        /\ content1 # content2
        /\ content1.content_id = content2.content_id
        /\ content1.timestamp = content2.timestamp
        /\ content1.deleted = TRUE
        /\ content2.deleted = FALSE
        /\ GetContentInfo(index_entries, content1.content_id).deleted = TRUE
        /\ GetContentInfo(index_entries, content1.content_id).timestamp = content1.timestamp

GetContentInfoCheck2 ==
    ~ \E content1, content2 \in index_entries:
        /\ content1 # content2
        /\ content1.content_id = content2.content_id
        /\ content1.timestamp < content2.timestamp
        /\ GetContentInfo(index_entries, content1.content_id) = content1

=============================================================================
\* Modification History
\* Last modified Sat Jun 20 18:23:20 CDT 2020 by pkj
\* Created Fri Apr 10 15:50:28 CDT 2020 by pkj
