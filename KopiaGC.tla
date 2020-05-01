------------------------------ MODULE KopiaGC ------------------------------
(*
    This is a spec to model behaviours of the interaction of Snapshot and GC processes in Kopia based on Julio's proposal of saving
    mark manifests and having a separate Repair & Discard phase.

    It is based out of my understanding of the code as of this commit in Julio's Kopia repo -
        https://github.com/julio-lopez/kopia/commit/132f823d4f1a321c88cdd5a4a880441800ef1c49

    General rules of thumb - Avoid using sequences where possible, using sets/bags can reduce state space.

    Things to possibly consider later -

    1. Had started with a bag of contents for snapshots. Reverted to using a set because
       a snapshot will not do anything in case the same content is to be written again. Because, it doesn't
       refresh the index from the blob store. This can be relaxed later if we have such a case.
    2. Similarly, not considering refresh of indices/ snapshot manifest midway in any process (snapshot/ gc / gc repair and discard).

*)

\* TODO - A deleted content entry can get removed during small index compaction if the entry is older than SkipDeletedOlderThan

EXTENDS Integers, Sequences, FiniteSets, Bags, TLC

CONSTANT
    NumContents, \* Restrict behaviours to snapshots that can contain contents with content IDs 0..NumContents-1
    MaxSnapshotsIssued, \* Maximum number of snapshots that can be issued. Constraint needed to restrict state space, else TLC will run forever
    MaxSnapshotTime, \* Maximum number of logical time steps a snapshot process can take. Post that it will not be able to mark itself "completed".
    MaxLogicalTime, \* Can't keep TLC running forever
    MaxGCMarksIssued,
    MaxGCRepairDiscardsIssued,
    MinGCMarkAge \* Only Mark phases with mark_phase.end_timestamp + MaxSnapshotTime (i.e., MinGCMarkAge can be >= MaxSnapshotTime) <= current_timestamp can be repaired.
    (* TODO - Explain how logical time is modeled, and how this field changes the scope of possible behaviours *)

VARIABLES
        (* Format - Set of content info entries.
            {
                [content_id |-> 0, deleted |-> TRUE/FALSE, timestamp |-> 0]
            }
        *)
        index,
        (* Format - Bag of records.
            {
             [status |-> "in_progress", "completed", "deleted", \* "completed" is analogous to the manifest for the snapshot being written to the store
              contents_written |-> Contents that have been written to the blob storage for the snapshot,
              index |-> Point in time view of index read at the start of snapshotting process, later this is updated on every
                flush of indices. Note that the update will only append flushed indices to this field. The indices are not refreshed from
                the global indices.
              index_blob_to_be_flushed |-> index blob that can be flushed to global index,
              start_timestamp |-> start_timestamp]
            }
        *)
        snapshots,
        (*
            {
                [
                    snapshots |-> Point in time view of the snapshots in the repository. Populated when this GC is triggered.
                    index |-> Point in time view of the global index.
                    contents_deleted |-> set of deleted content ids,
                    next_mark_mainfest_start_time |-> -1, \* When a new batch of contents to be deleted is started, this is set.
                        It is reset when a batch of deletes is flushed with the corresponding Mark manifest.
                    deletions_to_be_flushed |-> index blob of deletion entries that can be flushed to global index
                ]
            }
        *)
        gc_marks, \* Consider deleting gc_marks which have completed because they don't help in the decision of behaviours path later. Just exploding the state space.
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
                    index |-> Point in time view of the global index,
                    stage |-> "start"/ "repaired" / "populated_content_ids_to_discard",
                    content_ids_to_discard |-> {}
                ]
            }
        *)
        gc_repair_discards,
        current_timestamp
        \* actionPreformedInTimestep

KopiaInit == /\ snapshots = EmptyBag
             /\ current_timestamp = 0
             /\ index = {}
             /\ gc_marks = EmptyBag
             /\ gc_mark_manifests = EmptyBag
             /\ gc_repair_discards = EmptyBag
             \* /\ actionPreformedInTimestep = FALSE

NonEmptyPowerset(s) == (SUBSET s \ {{}})

IndexBlobsTypeOK == /\ IsABag(index)
                    /\ BagToSet(index) \in SUBSET(
                            [content_id: 0..NumContents-1,
                             deleted: {TRUE, FALSE},
                             timestamp: 0..MaxLogicalTime])

KopiaTypeOK == /\ IndexBlobsTypeOK
               /\ current_timestamp \in 0..MaxLogicalTime

HasContentInfo(idx_blobs, content_id) == LET matching_content_infos == {
                                                content_info \in idx_blobs: content_info.content_id = content_id}
                                         IN IF matching_content_infos # {} THEN TRUE
                                            ELSE FALSE

\* An index blob will have just one entry for each content ID. It can't have more than one. If this assumption breaks, change this logic.
\* Call this only if HasContentInfo is TRUE.
GetContentInfo(idx_blobs, content_id) ==
                                        LET matching_content_infos == {
                                                content_info \in idx_blobs: content_info.content_id = content_id}
                                            max_timestamp == CHOOSE timestamp \in {content_info.timestamp: content_info \in matching_content_infos}:
                                                                \A content_info \in matching_content_infos: timestamp >= content_info.timestamp
                                            latest_matching_content_infos == {
                                                content_info \in matching_content_infos: content_info.timestamp = max_timestamp}
                                        IN IF \E content_info \in latest_matching_content_infos: content_info.deleted = FALSE
                                           THEN CHOOSE content_info \in latest_matching_content_infos: content_info.deleted = FALSE
                                           ELSE CHOOSE content_info \in latest_matching_content_infos: TRUE

\* Define set of all content IDs in the idx_blobs irrespective of whether they are deleted or not.
ContentIDs(idx_blobs) == {content_info.content_id: content_info \in idx_blobs}

\* Either of the implementations of MergeIndices can be used. The first one compacts on the fly.

\* TODO - Handle the case where a deleted entry has the same timestamp as a normal entry for a given content ID. Or maybe don't handle it and leave it
\* as is? If left as is, at a single timestamp there can be a deleted and a normal entry for a single content ID. We can should the normal entry.
\*MergeIndices(idx_blobs_1, idx_blobs_2) == {content_info \in idx_blobs_1 \cup idx_blobs_2:
\*                                             /\
\*                                                \/ ~ HasContentInfo(idx_blobs_1, content_info.content_id)
\*                                                \/ GetContentInfo(idx_blobs_1, content_info.content_id).timestamp <= content_info.timestamp
\*                                             /\
\*                                                \/ ~ HasContentInfo(idx_blobs_2, content_info.content_id)
\*                                                \/ GetContentInfo(idx_blobs_2, content_info.content_id).timestamp <= content_info.timestamp}

\* TODO - For now keeping MergeIndcies a simple union. If possible, check the above commented version and use it.
MergeIndices(idx_blobs_1, idx_blobs_2) == idx_blobs_1 \cup idx_blobs_2

(* A thought (mostly incorrect) -
\* The case of a snapshot process being past its max time limit doesn't require explicit specification, it is as good as a smaller snapshot being completed
\* and then deleted. Note that this will miss the case where a snapshot in progress has written blobs but not indices, this can't be simulated using the
\* case of a smaller snapshot which is deleted, because deletion happens after completion which in turn is post all indices are flushed.

\* Also, the case of a partial snapshot flushing indices post its maximum time limit is not considered. If clocks can be arbitrary *)
 
WriteContents(snap) == /\ \E contents_to_write \in NonEmptyPowerset(0..NumContents-1 \ snap.contents_written):
                           \* Pick only those contents which have not been written till now. Even if a snapshot has the same content multiple times
                           \* it would only write it to the blob and add to index once.
                           LET contents_non_existing == {c_id \in contents_to_write:
                                                             (\/ ~ HasContentInfo(snap.index, c_id)
                                                              \/ GetContentInfo(snap.index, c_id).deleted)}
                               content_info_entries == [content_id: contents_non_existing,
                                                        timestamp: {current_timestamp},
                                                        deleted: {FALSE}]
                               updated_snapshot == [snap EXCEPT !.contents_written = snap.contents_written \cup contents_to_write,
                                                                !.index_blob_to_be_flushed = snap.index_blob_to_be_flushed \cup content_info_entries]
                           IN snapshots' = (snapshots (-) SetToBag({snap})) (+) SetToBag({updated_snapshot})
 
FlushIndex(snapshot) == 
                       LET
                           updated_snapshot == [snapshot EXCEPT !.index = MergeIndices(snapshot.index, snapshot.index_blob_to_be_flushed),
                                                                !.index_blob_to_be_flushed = {}]
                       IN
                           /\ snapshots' = (snapshots (-) SetToBag({snapshot})) (+) SetToBag({updated_snapshot})
                           /\ index' = MergeIndices(index, snapshot.index_blob_to_be_flushed)

TriggerSnapshot == /\ snapshots' = snapshots (+) SetToBag({[
                                        status |-> "in_progress", contents_written |-> {},
                                        index |-> index,
                                        index_blob_to_be_flushed |-> {},
                                        start_timestamp |-> current_timestamp]})

SnapshotProcessing ==
                     \/ \* Trigger a snapshot
                        /\ BagCardinality(snapshots) < MaxSnapshotsIssued
                        /\ TriggerSnapshot
                        /\ UNCHANGED <<index, current_timestamp, gc_marks, gc_mark_manifests, gc_repair_discards>>

                     \/
                        /\ \E snapshot \in BagToSet(snapshots):

                            \/  \* Write some contents to a blob
                                \* TODO - Should this be allowed post snapshot.start_timestamp + MaxSnapshotTime?
                                /\ snapshot.status = "in_progress"
                                /\ WriteContents(snapshot)
                                /\ UNCHANGED <<index, current_timestamp, gc_marks, gc_mark_manifests, gc_repair_discards>>

                            \/  \* Flush index
                                /\ snapshot.status = "in_progress"
                                /\ snapshot.index_blob_to_be_flushed # {}
                                /\ FlushIndex(snapshot)
                                /\ UNCHANGED <<current_timestamp, gc_marks, gc_mark_manifests, gc_repair_discards>>

                            \/  \* Complete snapshot
                                /\ snapshot.status = "in_progress"
                                /\ current_timestamp < snapshot.start_timestamp + MaxSnapshotTime
                                /\ snapshot.index_blob_to_be_flushed = {} \* There is nothing to be flushed
                                /\  LET updated_snapshot == [snapshot EXCEPT !.status = "completed"]
                                    IN  /\ UNCHANGED <<index, current_timestamp, gc_marks, gc_mark_manifests, gc_repair_discards>>
                                        /\ snapshots' = (snapshots (+) SetToBag({updated_snapshot})) (-) SetToBag({snapshot})

                            \/  \* Delete a snapshot
                                /\ snapshot.status = "completed"
                                /\  LET updated_snapshot == [snapshot EXCEPT !.status = "deleted"]
                                    IN  /\ snapshots' = (snapshots (+) SetToBag({updated_snapshot})) (-) SetToBag({snapshot})
                                        /\ UNCHANGED <<index, current_timestamp, gc_marks, gc_mark_manifests, gc_repair_discards>>

(* GC Mark phase *)
UnusedContentIDs(idx_blobs, snaps) == {content_id \in ContentIDs(idx_blobs):
                                                /\ ~ GetContentInfo(idx_blobs, content_id).deleted} \ UNION{snap.contents_written: snap \in snaps}

\* TriggerGC stores a point in time view of snapshots and the global index in the GC process record.
\* Consider only completed snapshots in TriggerGC, this helps in reducing state space. Reasoning - If all snapshots were kept in the GC process record,
\* two states with GC processes having the same set of completed snapshots but different set of non-completed snapshots would be differentiated,
\* even though the behaviour following those states won't be affected by the non-completed snapshots stored in the GC record (GC doesn't use the
\* information in non-completed records).

\* Consider only content_info entries which are old enough. Do it in Trigger instead of having a check in UnusedContentIDs (to
\* reduce state space). Here MaxSnapshotTime acts analogous to minContentAge in actual code.
TriggerGCMark == /\ gc_marks' = gc_marks (+) SetToBag({[snapshots |-> {snap \in BagToSet(snapshots): snap.status = "completed"},
                                                        index |-> {content_info \in index: current_timestamp >= (content_info.timestamp + MaxSnapshotTime)},
                                                        next_mark_mainfest_start_time |-> -1, \* Batch of contents to be deleted is not yet complete.
                                                        contents_deleted |-> {},
                                                        deletions_to_be_flushed |-> {}
                                                       ]})

\* TODO - If content iteration is in some specific order, the state space can be reduced. Right now the specification allows
\* deletion in any order.

\* Gap in spec and impl -
\* Right now the spec doesn't follow the iterator model (as in the impl) and allows picking any contents for deletion
\* which are to be deleted (selection model). Also, it allows cases of selection on the updated contents as compared to iteration
\* which iterates on a snapshot of the contents (Not exactly a strict snapshot, but a snapshot of the uncommitted contents is created and
\* then iterated on and then a snapshot of the commited contents is iterated on). But these details don't affect the selection/iteration model
\* as we are only adding deletion entries which are skipped in the selection/iteration process anyway.

DeleteContents(gc_mark) == /\ \E content_ids_to_delete \in NonEmptyPowerset(UnusedContentIDs(gc_mark.index, gc_mark.snapshots) \ gc_mark.contents_deleted):
                                \* Earlier gc.content_deleted was a set of contents and not content ids. That wasn't required and leads to a larger state space. TODO - Ponder on this.
                                LET contents_to_delete == [content_id: content_ids_to_delete, timestamp: {current_timestamp}, deleted: {TRUE}]
                                    updated_gc_mark == [gc_mark EXCEPT !.contents_deleted = gc_mark.contents_deleted \cup {content.content_id: content \in contents_to_delete},
                                                                       !.deletions_to_be_flushed = gc_mark.deletions_to_be_flushed \cup contents_to_delete,
                                                                       !.next_mark_mainfest_start_time = IF gc_mark.next_mark_mainfest_start_time = -1 THEN current_timestamp
                                                                                                         ELSE gc_mark.next_mark_mainfest_start_time]
                                IN
                                    gc_marks' = (gc_marks (-) SetToBag({gc_mark})) (+) SetToBag({updated_gc_mark})

FlushDeletedContents(gc_mark) ==  LET
                                     \* No need to update the gc_mark.index like we did for snapshots. This is because once a content is deleted by its
                                     \* presence in gc_mark.contents_deleted, it will never be checked again in the gc_mark.index.
                                     updated_gc_mark == [gc_mark EXCEPT !.deletions_to_be_flushed = {},
                                                                        !.next_mark_mainfest_start_time = -1]
                                  IN
                                     /\ gc_marks' = (gc_marks (-) SetToBag({gc_mark})) (+) SetToBag({updated_gc_mark})
                                     /\ index' = MergeIndices(index, gc_mark.deletions_to_be_flushed)
                                     /\ gc_mark_manifests' = gc_mark_manifests (+) SetToBag({[start_timestamp |-> gc_mark.next_mark_mainfest_start_time,
                                                                                    end_timestamp |-> current_timestamp,
                                                                                    deletes_flushed |-> {deletion.content_id: deletion \in gc_mark.deletions_to_be_flushed},
                                                                                    snapshots |-> gc_mark.snapshots]})

GC_Mark == \/
              \* Trigger GC Mark phase. Load the index blobs and completed snapshots (not all, to save on state space) at the current_timestamp.
              /\ BagCardinality(gc_marks) < MaxGCMarksIssued
              /\ TriggerGCMark
              /\ UNCHANGED <<snapshots, index, current_timestamp, gc_mark_manifests, gc_repair_discards>>
           \/
              \* Delete some contents which are in the index blobs, but not referenced by the snapshots.
              /\ \E gc_mark \in BagToSet(gc_marks):
                  /\ DeleteContents(gc_mark)
                  /\ UNCHANGED <<snapshots, index, current_timestamp, gc_mark_manifests, gc_repair_discards>>
           \/ \* Flush index blob of deleted entries along with the mark phase's manifest
              /\ \E gc \in BagToSet(gc_marks):
                  /\ gc.deletions_to_be_flushed # {}
                  /\ FlushDeletedContents(gc)
                  /\ UNCHANGED <<snapshots, current_timestamp, gc_repair_discards>>

(* Repair and Discard phase *)
TriggerGCRepairDiscard == /\ gc_repair_discards' = gc_repair_discards (+) SetToBag({[snapshots |-> {snap \in BagToSet(snapshots): snap.status = "completed"},
                                                        mark_manifests |-> {manifest \in BagToSet(gc_mark_manifests): current_timestamp >= (manifest.end_timestamp + MinGCMarkAge)},
                                                        index |-> index,
                                                        stage |-> "start",
                                                        content_ids_to_discard |-> {}
                                                       ]})

Repair(repair_discard) == LET
                             \* Set of snapshots which were not seen by the mark manifests.
                             snapshots_to_check == UNION{repair_discard.snapshots \ manifest.snapshots: manifest \in repair_discard.mark_manifests}
                             contents_to_maybe_repair == UNION{snapshot.contents_written: snapshot \in snapshots_to_check}
                             contents_to_repair == {content_id \in contents_to_maybe_repair:
                                                        /\ HasContentInfo(repair_discard.index, content_id)
                                                        /\ GetContentInfo(repair_discard.index, content_id).deleted = TRUE}
                             index_to_flush == [content_id: contents_to_repair, timestamp: {current_timestamp}, deleted: {FALSE}]
                             updated_repair_discard == [repair_discard EXCEPT !.stage = "repaired"]
                          IN
                             /\ index' = MergeIndices(index, index_to_flush)
                             /\ gc_repair_discards' = (gc_repair_discards (-) SetToBag({repair_discard})) (+) SetToBag({updated_repair_discard})

PopulateContentIDsToDiscard(repair_discard) ==
                          LET
                             marked_content_ids == UNION{manifest.deletes_flushed: manifest \in repair_discard.mark_manifests}
                             content_ids_to_discard == {content_id \in marked_content_ids:
                                                          /\ HasContentInfo(repair_discard.index, content_id)
                                                          /\ GetContentInfo(repair_discard.index, content_id).deleted}
                             updated_repair_discard == [repair_discard EXCEPT !.content_ids_to_discard = content_ids_to_discard,
                                                                              !.stage = "populated_content_ids_to_discard"]
                          IN
                             gc_repair_discards' = (gc_repair_discards (-) SetToBag({repair_discard})) (+) SetToBag({updated_repair_discard})


Discard(repair_discard) == LET
                              all_contents_to_remove_from_global_index ==
                                {content \in repair_discard.index: content.content_id \in repair_discard.content_ids_to_discard}
                           IN
                              /\ \E contents_to_remove_from_global_index \in NonEmptyPowerset(all_contents_to_remove_from_global_index):
                                   \* With this we are simulating deletions of chunks of contents in the indices. Contents might be
                                   \* discarded in any size of batches. In the actual systems, contents in the same index blob
                                   \* are discarded together (the index blob is deleted after the comapacted index is written).
                                   \* In the actual system an index blob is deleted at once but with this random chunk deletion
                                   \* that we have done, we are allowing more behaviours than are allowed in actual i.e., we are also
                                   \* allowing behaviours with contents from different index blobs deleted together and also the case
                                   \* where contents to be discarded from the same index blob are not discarded together.
                                   /\ index' = index \ contents_to_remove_from_global_index
                                   /\ LET
                                         updated_repair_discard == [repair_discard EXCEPT !.index = repair_discard.index \ contents_to_remove_from_global_index]
                                      IN
                                         gc_repair_discards' = (gc_repair_discards (-) SetToBag({repair_discard})) (+) SetToBag({updated_repair_discard})

\*RemoveManifests(repair_discard) == LET
\*                                      all_contents_to_remove_from_global_index ==
\*                                        {content \in repair_discard.index: content.content_id \in repair_discard.content_ids_to_discard}
\*                                   IN
\*                                      /\ all_contents_to_remove_from_global_index = {} \* All contents to be discarded have been discarded. Now, delete the mark manifests.
\*                                      /\ gc_mark_manifests' = gc_mark_manifests (-) repair_discard.mark_manifests

GC_Repair_Discard == \/
                        \* Trigger GC Repair and Discard phase. Load the completed snapshots and mark manifests (older than the safety threshold mentioned earlier).
                        /\ BagCardinality(gc_repair_discards) < MaxGCRepairDiscardsIssued
                        /\ TriggerGCRepairDiscard
                        /\ UNCHANGED <<snapshots, index, current_timestamp, gc_marks, gc_mark_manifests>>
                     \/
                        /\ \E repair_discard \in BagToSet(gc_repair_discards):
                             \/ \* Repair contents
                                /\ repair_discard.stage = "start"
                                /\ Repair(repair_discard)
                                /\ UNCHANGED <<snapshots, current_timestamp, gc_marks, gc_mark_manifests>>
                             \/ \* Populate content IDs to discard
                                /\ repair_discard.stage = "repaired"
                                /\ PopulateContentIDsToDiscard(repair_discard)
                                /\ UNCHANGED <<snapshots, current_timestamp, gc_marks, gc_mark_manifests, index>>
                             \/ \* Discard contents
                                /\ repair_discard.stage = "populated_content_ids_to_discard"
                                /\ Discard(repair_discard)
                                /\ UNCHANGED <<snapshots, current_timestamp, gc_marks, gc_mark_manifests>>
\*                             \/ \* Remove manifests if all contents to be removed in the discard phase have been removed
\*                                /\ repair_discard.stage = "populated_content_ids_to_discard"
\*                                /\ RemoveManifests(repair_discard)
\*                                /\ UNCHANGED <<snapshots, current_timestamp, gc_marks, index, gc_repair_discards>>

KopiaNext == \/
                /\ SnapshotProcessing
             \/
                /\ GC_Mark
             \/
                /\ GC_Repair_Discard
             \/
                \* Tick time forward.
                /\ current_timestamp < MaxLogicalTime
                /\ current_timestamp' = current_timestamp + 1
                /\ UNCHANGED <<index, snapshots, gc_marks, gc_mark_manifests, gc_repair_discards>>

(* Invariants and safety check *)

\* TODO - In this specification a content being marked as deleted is as good as the content not existing i.e., removed by compaction (Stmnt A). This is different
\* from what deletion means in the GC2 spec (which is the actual meaning of the deleted=True marker on a content info) (Stmnt B).
\* Actually, I have written this spec with the meaning of stmnt A in mind. This doesn't change anything for us, but for clarity, I will refactor later to
\* indicate the true meaning as per Kopia code i.e., Stmnt B.

GCInvariant ==  \A snap \in {snap \in BagToSet(snapshots): snap.status = "completed"}:
                  /\ \A content_id \in snap.contents_written:
                     /\ HasContentInfo(index, content_id)

GetContentInfoCheck == ~ \E content1, content2 \in index:
                           /\ content1 # content2
                           /\ content1.content_id = content2.content_id
                           /\ content1.timestamp = content2.timestamp
                           /\ content1.deleted = TRUE
                           /\ content2.deleted = FALSE
                           /\ GetContentInfo(index, content1.content_id).deleted = TRUE

GetContentInfoCheck2 == ~ \E content1, content2 \in index:
                           /\ content1 # content2
                           /\ content1.content_id = content2.content_id
                           /\ content1.timestamp < content2.timestamp
                           /\ GetContentInfo(index, content1.content_id) = content1

=============================================================================
\* Modification History
\* Last modified Fri May 01 12:05:50 CDT 2020 by pkj
\* Created Fri Apr 10 15:50:28 CDT 2020 by pkj
