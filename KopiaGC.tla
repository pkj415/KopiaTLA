------------------------------ MODULE KopiaGC ------------------------------
(*
    This is a spec to model behaviours of the interaction of Snapshot and GC processes in Kopia.
    It is based out of my understanding of the code as of this commit - 9c3d419bc396c0446f21c68813ca195196843eab

    General rules of thumb - Avoid using sequences where possible, using sets/bags can reduce state space.

    Things to possibly consider later -

    1. Had started with a bag of contents for snapshots. Reverted to using a set because
       a snapshot will not do anything in case the same content is to be written again. Because, it doesn't
       refresh the index from the blob store. This can be relaxed later if we have such a case.
    2. Similarly, not considering refresh of indices and snapshot manifest midway in a GC process.

*)

\* TODO - A deleted content entry can get removed during small index compaction if the entry is older than SkipDeletedOlderThan

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
                    deletions_to_be_flushed |-> index blob of deletion entries that can be flushed to global index
                ]
            }
        *)
        gcs,
        current_timestamp
        \* actionPreformedInTimestep

KopiaInit == /\ snapshots = EmptyBag
             /\ current_timestamp = 0
             /\ index = {}
             /\ gcs = EmptyBag
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
                        /\ UNCHANGED <<index, current_timestamp, gcs>>

                     \/
                        /\ \E snapshot \in BagToSet(snapshots):

                            \/  \* Write some contents to a blob
                                \* TODO - Should this be allowed post snapshot.start_timestamp + MaxSnapshotTime?
                                /\ snapshot.status = "in_progress"
                                /\ WriteContents(snapshot)
                                /\ UNCHANGED <<index, current_timestamp, gcs>>

                            \/  \* Flush index
                                /\ snapshot.status = "in_progress"
                                /\ snapshot.index_blob_to_be_flushed # {}
                                /\ FlushIndex(snapshot)
                                /\ UNCHANGED <<current_timestamp, gcs>>

                            \/  \* Complete snapshot
                                /\ snapshot.status = "in_progress"
                                /\ current_timestamp < snapshot.start_timestamp + MaxSnapshotTime
                                /\ snapshot.index_blob_to_be_flushed = {} \* There is nothing to be flushed
                                /\  LET updated_snapshot == [snapshot EXCEPT !.status = "completed"]
                                    IN  /\ UNCHANGED <<index, current_timestamp, gcs>>
                                        /\ snapshots' = (snapshots (+) SetToBag({updated_snapshot})) (-) SetToBag({snapshot})

                            \/  \* Delete a snapshot
                                /\ snapshot.status = "completed"
                                /\  LET updated_snapshot == [snapshot EXCEPT !.status = "deleted"]
                                    IN  /\ snapshots' = (snapshots (+) SetToBag({updated_snapshot})) (-) SetToBag({snapshot})
                                        /\ UNCHANGED <<index, current_timestamp, gcs>>

UnusedContentIDs(idx_blobs, snaps) == {content_id \in ContentIDs(idx_blobs):
                                                /\ ~ GetContentInfo(idx_blobs, content_id).deleted} \ UNION{snap.contents_written: snap \in snaps}

\* TriggerGC stores a point in time view of snapshots and the global index in the GC process record.
\* Consider only completed snapshots in TriggerGC, this helps in reducing state space. Reasoning - If all snapshots were kept in the GC process record,
\* two states with GC processes having the same set of completed snapshots but different set of non-completed snapshots would be differentiated,
\* even though the behaviour following those states won't be affected by the non-completed snapshots stored in the GC record (GC doesn't use the
\* information in non-completed records).

\* Consider only content_info entries which are old enough. Do it in Trigger instead of having a check in UnusedContentIDs (to
\* reduce state space). Here MaxSnapshotTime acts analogous to minContentAge in actual code.
TriggerGC ==
              /\ gcs' = gcs (+) SetToBag({[snapshots |-> {snap \in BagToSet(snapshots): snap.status = "completed"},
                                        index |-> {content_info \in index: current_timestamp >= (content_info.timestamp + MaxSnapshotTime)},
                                        contents_deleted |-> {},
                                        deletions_to_be_flushed |-> {}
                                       ]})

\* TODO - If content iteration is in some specific order, the state space can be reduced. Right now the specification allows
\* deletion in any order.
DeleteContents(gc) == /\ \E content_ids_to_delete \in
                              NonEmptyPowerset(UnusedContentIDs(gc.index, gc.snapshots) \ gc.contents_deleted): \* Earlier gc.content_deleted was a set of contents and not content ids. That wasn't required and leads to a larger state space. TODO - Ponder on this.
                                LET contents_to_delete == [content_id: content_ids_to_delete, timestamp: {current_timestamp}, deleted: {TRUE}]
                                    updated_gc == [gc EXCEPT !.contents_deleted = gc.contents_deleted \cup {content.content_id: content \in contents_to_delete},
                                                             !.deletions_to_be_flushed = gc.deletions_to_be_flushed \cup contents_to_delete]
                                IN
                                    /\ gcs' = (gcs (-) SetToBag({gc})) (+) SetToBag({updated_gc})

FlushDeletedContents(gc) ==  LET
                                \* No need to update the gc.index like we did for snapshots. This is because once a content is deleted by its
                                \* presence in gc.contents_deleted, it will never be checked again in the gc.index.
                                updated_gc == [gc EXCEPT !.deletions_to_be_flushed = {}]
                             IN
                                /\ gcs' = (gcs (-) SetToBag({gc})) (+) SetToBag({updated_gc})
                                /\ index' = MergeIndices(index, gc.deletions_to_be_flushed)

GC_Processing == \/
                    \* Trigger GC. Load the index blobs and completed snapshots (not all, to save on state space) at the current_timestamp.
                    /\ BagCardinality(gcs) < MaxGCsIssued
                    /\ TriggerGC
                    /\ UNCHANGED <<snapshots, index, current_timestamp>>
                 \/
                    \* Delete some contents which are in the index blobs, but not referenced by the snapshots.
                    /\ \E gc \in BagToSet(gcs):
                        /\ DeleteContents(gc)
                        /\ UNCHANGED <<snapshots, index, current_timestamp>>
                 \/ \* Flush index blob of deleted entries
                    /\ \E gc \in BagToSet(gcs):
                        /\ gc.deletions_to_be_flushed # {}
                        /\ FlushDeletedContents(gc)
                        /\ UNCHANGED <<snapshots, current_timestamp>>

KopiaNext == \/ 
                /\ SnapshotProcessing
             \/
                /\ GC_Processing
             \/
                \* Tick time forward.
                /\ current_timestamp < MaxLogicalTime
                /\ current_timestamp' = current_timestamp + 1
                /\ UNCHANGED <<index, snapshots, gcs>>

(* Invariants and safety check *)

\* TODO - In this specification a content being marked as deleted is as good as the content not existing i.e., removed by compaction (Stmnt A). This is different
\* from what deletion means in the GC2 spec (which is the actual meaning of the deleted=True marker on a content info) (Stmnt B).
\* Actually, I have written this spec with the meaning of stmnt A in mind. This doesn't change anything for us, but for clarity, I will refactor later to
\* indicate the true meaning as per Kopia code i.e., Stmnt B.

GCInvariant ==  \A snap \in {snap \in BagToSet(snapshots): snap.status = "completed"}:
                  /\ \A content_id \in snap.contents_written:
                     /\ HasContentInfo(index, content_id)
                     /\ ~ GetContentInfo(index, content_id).deleted

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
\* Last modified Fri May 01 07:56:47 CDT 2020 by pkj
\* Created Fri Apr 10 15:50:28 CDT 2020 by pkj
