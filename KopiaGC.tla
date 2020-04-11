------------------------------ MODULE KopiaGC ------------------------------
(* Blob store
    Avoid using sequences where possible, using sets can reduce state space.

Had started with a bag of contents for a snapshots. Reverted to using a set because
a snapshot will not do anything in case the same content is to be written again. Because, it doesn't
refresh the index from the blob store. This can be relaxed later if we have such a case.

Index blob entries don't have timestamp order. This is because the Sequence of index_blobs mimicks
time order, and TLC generates all possibles states in the state spaces.
*)

EXTENDS Integers, Sequences, FiniteSets, Bags, TLC

CONSTANT
    NumContents, \* Restrict behaviours to snapshots that can contain contents with content IDs 0..NumContents-1
    MaxSnapshotsIssued, \* Maximum number of snapshots that can be issued. Constraint needed to restrict state space, else TLC will run forever
    MaxSnapshotTime, \* Maximum number of logical time steps a snapshot process can take. Post that it will not be processed.
    MaxLogicalTime \* Can't keep TLC running forever
    (* TODO - Explain how logical time is modeled, and how this field changes the scope of possible behaviours *)

VARIABLES
        (* Format - Bag of index blobs each having a set (or bag? is it a bag in Kopia?) of records which specify contents.
            TODO - Check if it can all be part of one sequence. This will reduce the number of unique states.
            {
                {[content_id |-> 0, deleted |-> TRUE/FALSE, timestamp |-> 0]}
            }
        *)
        index_blobs,
        (* Format - Bag of records.
            {
             [status |-> "in_progress", "completed", "deleted",
              contents_written |-> Contents that have written to the blob storage for the snapshot,
              index_blobs |-> snapshot of index blobs read at the start of snapshotting process, later this is updated on every flush of indices.
              index_blob_to_be_flushed |-> index blob that can be flushed to global index_blobs,
              start_timestamp |-> start_timestamp]
            }
        *)
        snapshots,
        current_timestamp

KopiaInit == /\ snapshots = EmptyBag
             /\ current_timestamp = 0
             /\ index_blobs = EmptyBag

NonEmptyPowerset(s) == (SUBSET s \ {{}})

IndexBlobsTypeOK == /\ IsABag(index_blobs)
                    /\ BagToSet(index_blobs) \in SUBSET(
                            [content_id: 0..NumContents-1,
                             deleted: {TRUE, FALSE},
                             timestamp: 0..MaxLogicalTime])

KopiaTypeOK == /\ IndexBlobsTypeOK
               /\ current_timestamp \in 0..MaxLogicalTime

HasContentInfo(idx_blobs, content_id) == LET matching_content_infos == UNION({
                                            UNION{
                                                IF content_info.content_id = content_id THEN {content_info}
                                                ELSE {} : content_info \in idx_blob} : idx_blob \in BagToSet(idx_blobs)})
                                         IN IF matching_content_infos # {} THEN TRUE
                                            ELSE FALSE

\* An index blob will have just one entry for each content ID. It can't have more than one. If this assumption breaks, change this logic.
\* Call only if HasContentInfo is TRUE
GetContentInfo(idx_blobs, content_id) ==
                                        LET matching_content_infos == UNION({
                                            UNION{
                                                IF content_info.content_id = content_id THEN {content_info}
                                                ELSE {} : content_info \in idx_blob} : idx_blob \in BagToSet(idx_blobs)})
                                        IN CHOOSE content_info \in matching_content_infos:
                                                \A c \in matching_content_infos: c.timestamp <= content_info.timestamp

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
                           updated_snapshot == [snapshot EXCEPT !.index_blobs = snapshot.index_blobs (+) SetToBag({snapshot.index_blob_to_be_flushed}),
                                                                !.index_blob_to_be_flushed = {}]
                       IN
                           /\ snapshots' = (snapshots (-) SetToBag({snapshot})) (+) SetToBag({updated_snapshot})
                           /\ index_blobs' = index_blobs (+) SetToBag({snapshot.index_blob_to_be_flushed})

TriggerSnapshot == /\ snapshots' = snapshots (+) SetToBag({[
                                        status |-> "in_progress", contents_written |-> {},
                                        index_blobs |-> index_blobs, \* Can this be made reduced to a set instead of a bag?
                                        index_blob_to_be_flushed |-> {},
                                        start_timestamp |-> current_timestamp]})

KopiaNext == 
             \/ 
                \* Trigger a snapshot
                /\ BagCardinality(snapshots) < MaxSnapshotsIssued
                /\ TriggerSnapshot
                /\ UNCHANGED <<index_blobs, current_timestamp>>
\*                /\ Print("Trigger a snapshot", TRUE)
             \/ 
                /\ \E snapshot \in BagToSet(snapshots):
                    \* Write some contents to a blob
                    \/  /\ snapshot.status = "in_progress"
                        /\ WriteContents(snapshot)
                        /\ UNCHANGED <<index_blobs, current_timestamp>>
\*                        /\ Print("Write come contents", TRUE)
                    \* Flush index 
                    \/  /\ snapshot.status = "in_progress"
                        /\ snapshot.index_blob_to_be_flushed # {}
                        /\ FlushIndex(snapshot)
                        /\ UNCHANGED <<current_timestamp>>
\*                        /\ Print("Flush Index", TRUE)
                    \* Complete snapshot
                    \/  
                        /\ snapshot.status = "in_progress"
                        /\ snapshot.start_timestamp + MaxSnapshotTime <= current_timestamp
                        /\ snapshot.index_blob_to_be_flushed = {} \* There is nothing to be flushed
                        /\  LET updated_snapshot == [snapshot EXCEPT !.status = "completed"]
                            IN  /\ UNCHANGED <<index_blobs, current_timestamp>>
                                /\ snapshots' = (snapshots (+) SetToBag({updated_snapshot})) (-) SetToBag({snapshot})
\*                        /\ Print("Complete snapshot", TRUE)
                    \* Delete a snapshot
                    \/ 
                        /\ snapshot.status = "completed"
                        /\  LET updated_snapshot == [snapshot EXCEPT !.status = "deleted"]
                            IN  /\ snapshots' = (snapshots (+) SetToBag({updated_snapshot})) (-) SetToBag({snapshot})
                                /\ UNCHANGED <<index_blobs, current_timestamp>>
\*                        /\ Print("Delete snapshot", TRUE)
                    \* Tick time forward
                    \/
                        /\ current_timestamp < MaxLogicalTime
                        /\ current_timestamp' = current_timestamp + 1
                        /\ UNCHANGED <<index_blobs, snapshots>>
\*                        /\ Print("Tick time forward", TRUE)

=============================================================================
\* Modification History
\* Last modified Sat Apr 11 10:09:40 CDT 2020 by pkj
\* Created Fri Apr 10 15:50:28 CDT 2020 by pkj
