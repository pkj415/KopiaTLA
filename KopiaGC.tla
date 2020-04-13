------------------------------ MODULE KopiaGC ------------------------------
(*
    General rules of thumb - Avoid using sequences where possible, using sets/bags can reduce state space.

    Things to possibly consider later -

    1. Had started with a bag of contents for snapshots. Reverted to using a set because
       a snapshot will not do anything in case the same content is to be written again. Because, it doesn't
       refresh the index from the blob store. This can be relaxed later if we have such a case.
    2. Similarly, not considering refresh of indices and snapshot manifest midway in a GC process.

*)

EXTENDS Integers, Sequences, FiniteSets, Bags, TLC

CONSTANT
    NumContents, \* Restrict behaviours to snapshots that can contain contents with content IDs 0..NumContents-1
    MaxSnapshotsIssued, \* Maximum number of snapshots that can be issued. Constraint needed to restrict state space, else TLC will run forever
    MaxSnapshotTime, \* Maximum number of logical time steps a snapshot process can take. Post that it will not be able to mark itself "completed".
    MaxLogicalTime, \* Can't keep TLC running forever
    MaxGCsIssued
    (* TODO - Explain how logical time is modeled, and how this field changes the scope of possible behaviours *)

VARIABLES
        (* Format - Set of content info entries.
            {
                [content_id |-> 0, deleted |-> TRUE/FALSE, timestamp |-> 0]
            }
        *)
        index_blobs,
        (* Format - Bag of records.
            {
             [status |-> "in_progress", "completed", "deleted", \* "completed" is analogous to the manifest for the snapshot being written to the store
              contents_written |-> Contents that have been written to the blob storage for the snapshot,
              index_blobs |-> Point in time view of index blobs read at the start of snapshotting process, later this is updated on every
                flush of indices. Note that the update will only append flushed indices to this field. The indices are not refreshed from
                the global indices.
              index_blob_to_be_flushed |-> index blob that can be flushed to global index_blobs,
              start_timestamp |-> start_timestamp]
            }
        *)
        snapshots,
        (*
            {
                [
                    snapshots |-> Point in time view of the snapshots in the repository. Populated when this GC is triggered.
                    index_blobs |-> Point in time view of the global index_blobs.
                    contents_deleted |-> {[content_id |-> 0, deleted |-> TRUE, timestamp |-> 0]},
                    deletions_to_be_flushed |-> index blob of deletion entries that can be flushed to global index_blobs
                ]
            }
        *)
        gcs,
        current_timestamp,
        actionPreformedInTimestep

KopiaInit == /\ snapshots = EmptyBag
             /\ current_timestamp = 0
             /\ index_blobs = {}
             /\ gcs = EmptyBag
             /\ actionPreformedInTimestep = FALSE

NonEmptyPowerset(s) == (SUBSET s \ {{}})

IndexBlobsTypeOK == /\ IsABag(index_blobs)
                    /\ BagToSet(index_blobs) \in SUBSET(
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
\* TODO - Also, in case a deleted entry is present along with a normal entry at the same timestamp, consider
\* the non-deleted one.
GetContentInfo(idx_blobs, content_id) ==
                                        LET matching_content_infos == {
                                                content_info \in idx_blobs: content_info.content_id = content_id}
                                        IN CHOOSE content_info \in matching_content_infos:
                                                \A c \in matching_content_infos: c.timestamp <= content_info.timestamp

\* Define set of all content IDs in the idx_blobs irrespective of whether they are deleted or not.
ContentIDs(idx_blobs) == {content_info.content_id: content_info \in idx_blobs}

\* TODO - Handle the case where a deleted entry has the same timestamp as a normal entry for a given content ID. Or maybe don't handle it and leave it
\* as is?
MergeIndices(idx_blobs_1, idx_blobs_2) == {content_info \in idx_blobs_1 \cup idx_blobs_2:
                                             /\
                                                \/ ~ HasContentInfo(idx_blobs_1, content_info.content_id)
                                                \/ GetContentInfo(idx_blobs_1, content_info.content_id).timestamp <= content_info.timestamp
                                             /\
                                                \/ ~ HasContentInfo(idx_blobs_2, content_info.content_id)
                                                \/ GetContentInfo(idx_blobs_2, content_info.content_id).timestamp <= content_info.timestamp}

(* A thought (mostly incorrect) -
\* The case of a snapshot process being past its max time limit doesn't require explicit specification, it is as good as a smaller snapshot being completed
\* and then deleted. Note that this will miss the case where a snapshot in progress has written blobs but not indices, this can't be simulated using the
\* case of a smaller snapshot which is deleted, because deletion happens after completion which in turn is post all indices are flushed.

\* Also, the case of a partial snapshot flushing indices post its maximum time limit is not considered. If clocks can be arbitrary *)
 
WriteContents(snap) == /\ \E contents_to_write \in NonEmptyPowerset(0..NumContents-1 \ snap.contents_written):
                           \* Pick only those contents which have not been written till now. Even if a snapshot has the same content multiple times
                           \* it would only write it to the blob and add to index once.
                           LET contents_non_existing == {c_id \in contents_to_write:
                                                             (\/ ~ HasContentInfo(snap.index_blobs, c_id)
                                                              \/ GetContentInfo(snap.index_blobs, c_id).deleted)}
                               content_info_entries == [content_id: contents_non_existing,
                                                        timestamp: {current_timestamp},
                                                        deleted: {FALSE}]
                               updated_snapshot == [snap EXCEPT !.contents_written = snap.contents_written \cup contents_to_write,
                                                                !.index_blob_to_be_flushed = snap.index_blob_to_be_flushed \cup content_info_entries]
                           IN snapshots' = (snapshots (-) SetToBag({snap})) (+) SetToBag({updated_snapshot})
 
FlushIndex(snapshot) == 
                       LET
                           updated_snapshot == [snapshot EXCEPT !.index_blobs = MergeIndices(snapshot.index_blobs, snapshot.index_blob_to_be_flushed),
                                                                !.index_blob_to_be_flushed = {}]
                       IN
                           /\ snapshots' = (snapshots (-) SetToBag({snapshot})) (+) SetToBag({updated_snapshot})
                           /\ index_blobs' = MergeIndices(snapshot.index_blobs, snapshot.index_blob_to_be_flushed)

TriggerSnapshot == /\ snapshots' = snapshots (+) SetToBag({[
                                        status |-> "in_progress", contents_written |-> {},
                                        index_blobs |-> index_blobs,
                                        index_blob_to_be_flushed |-> {},
                                        start_timestamp |-> current_timestamp]})

SnapshotProcessing ==
                     \/ \* Trigger a snapshot
                        /\ BagCardinality(snapshots) < MaxSnapshotsIssued
                        /\ TriggerSnapshot
                        /\ UNCHANGED <<index_blobs, current_timestamp, gcs>>

                     \/
                        /\ \E snapshot \in BagToSet(snapshots):

                            \/  \* Write some contents to a blob
                                /\ snapshot.status = "in_progress"
                                /\ WriteContents(snapshot)
                                /\ UNCHANGED <<index_blobs, current_timestamp, gcs>>

                            \/  \* Flush index
                                /\ snapshot.status = "in_progress"
                                /\ snapshot.index_blob_to_be_flushed # {}
                                /\ FlushIndex(snapshot)
                                /\ UNCHANGED <<current_timestamp, gcs>>

                            \/  \* Complete snapshot
                                /\ snapshot.status = "in_progress"
                                /\ snapshot.start_timestamp + MaxSnapshotTime <= current_timestamp
                                /\ snapshot.index_blob_to_be_flushed = {} \* There is nothing to be flushed
                                /\  LET updated_snapshot == [snapshot EXCEPT !.status = "completed"]
                                    IN  /\ UNCHANGED <<index_blobs, current_timestamp, gcs>>
                                        /\ snapshots' = (snapshots (+) SetToBag({updated_snapshot})) (-) SetToBag({snapshot})

                            \/  \* Delete a snapshot
                                /\ snapshot.status = "completed"
                                /\  LET updated_snapshot == [snapshot EXCEPT !.status = "deleted"]
                                    IN  /\ snapshots' = (snapshots (+) SetToBag({updated_snapshot})) (-) SetToBag({snapshot})
                                        /\ UNCHANGED <<index_blobs, current_timestamp, gcs>>

\* TriggerGC stores a point in time view of snapshots and the global index_blobs in the GC process record.
\* Consider only completed snapshots in TriggerGC, this helps in reducing state space. Reasoning - If all snapshots were kept in the GC process record,
\* two states with GC processes having the same set of completed snapshots but different set of non-completed snapshots would be differentiated,
\* even though the behaviour following those states won't be affected by the non-completed snapshots stored in the GC record (GC doesn't use the
\* information in non-completed records).
TriggerGC ==
              gcs' = gcs (+) SetToBag({[snapshots |-> {snap \in BagToSet(snapshots): snap.status = "completed"},
                                        index_blobs |-> index_blobs,
                                        contents_deleted |-> {},
                                        deletions_to_be_flushed |-> {}
                                       ]})

UnusedContentIDs(idx_blobs, snaps) == {content_id \in ContentIDs(idx_blobs):
                                                /\ ~ GetContentInfo(idx_blobs, content_id).deleted} \ UNION{snap.contents_written: snap \in snaps}

DeleteContents(gc) == /\ \E content_ids_to_delete \in
                              NonEmptyPowerset(UnusedContentIDs(gc.index_blobs, gc.snapshots) \ {content_info.content_id : content_info \in gc.contents_deleted}):
                                LET contents_to_delete == [content_id: content_ids_to_delete, timestamp: {current_timestamp}, deleted: {TRUE}]
                                    updated_gc == [gc EXCEPT !.contents_deleted = gc.contents_deleted \cup contents_to_delete,
                                                             !.deletions_to_be_flushed = contents_to_delete]
                                IN
                                    /\ gcs' = (gcs (-) SetToBag({gc})) (+) SetToBag({updated_gc})

FlushDeletedContents(gc) ==  LET
                                \* No need to update the gc.index_blobs like we did for snapshots. This is because once a content is deleted by its
                                \* presence in gc.contents_deleted, it will never be checked again in the gc.index_blobs.
                                updated_gc == [gc EXCEPT !.deletions_to_be_flushed = {}]
                             IN
                                /\ gcs' = (gcs (-) SetToBag({gc})) (+) SetToBag({updated_gc})
                                /\ index_blobs' = MergeIndices(index_blobs, gc.deletions_to_be_flushed)

GC_Processing == \/
                    \* Trigger GC. Load the index blobs and completed snapshots (not all, to save on state space) at the current_timestamp.
                    /\ BagCardinality(gcs) < MaxGCsIssued
                    /\ TriggerGC
                    /\ UNCHANGED <<snapshots, index_blobs, current_timestamp>>
\*                 \/
\*                    \* Delete some contents which are in the index blobs, but not referenced by the snapshots.
\*                    /\ \E gc \in BagToSet(gcs):
\*                        /\ DeleteContents(gc)
\*                        /\ UNCHANGED <<snapshots, index_blobs, current_timestamp>>
\*                 \/ \* Flush index blob of deleted entries
\*                    /\ \E gc \in BagToSet(gcs):
\*                        /\ gc.deletions_to_be_flushed # {}
\*                        /\ FlushDeletedContents(gc)
\*                        /\ UNCHANGED <<snapshots, current_timestamp>>

KopiaNext == \/ 
                /\ SnapshotProcessing
                /\ actionPreformedInTimestep' = TRUE
             \/
                /\ GC_Processing
                /\ actionPreformedInTimestep' = TRUE
             \/ \* Tick time forward. Increment logical time only if some state change occured in the time step. If not, don't increment.
                \* This trick helps reduce state space, while not missing out on important behaviours (we don't need to consider no-op behaviours). 
                /\ current_timestamp < MaxLogicalTime
                /\ actionPreformedInTimestep = TRUE
                /\ current_timestamp' = current_timestamp + 1
                /\ actionPreformedInTimestep' = FALSE
                /\ UNCHANGED <<index_blobs, snapshots, gcs>>
                \* /\ Print("Tick time forward", TRUE)
=============================================================================
\* Modification History
\* Last modified Mon Apr 13 00:26:44 CDT 2020 by pkj
\* Created Fri Apr 10 15:50:28 CDT 2020 by pkj
