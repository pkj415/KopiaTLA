------------------------------ MODULE KopiaGC ------------------------------
(* Blob store
    - ListBlobsConsistent for one prefix
    
    Filesystem - 
        - Put is consistent
        - Delete is consistent
    
    GCS -
        - Put is consistent
        - Delete is consistent

    Blob compaction -
        - Delete if blob has no referenced content
        
Create a time ticker to mimick time related assumptions.

Had started with a bag of contents for a snapshots. Reverted to using a set because
a snapshot will not do anything in case the same content is to be written again. Because, it doesn't
refresh the index from the blob store. This can be relaxed later if we have such a case.

Index blob entries don't have timestamp order. This is because the Sequence of index_blobs mimicks
time order, and TLC generates all possibles states in the state spaces.
*)

EXTENDS Integers, Sequences, FiniteSets, Bags, TLC

CONSTANT
    NumContents,
\*    NumBlobs, Required?
\*    MaxSnapshotsInProgress, \* Required ?
    MaxSnapshotsIssued, \* Constraint to restrict state space. Else TLC will run forever
    MaxSnapshotTime
\*    MaxSnapshotDeletions \* Constraint to restrict state space. Else TLC will run forever, Required?
\*    MaxCntOfContentInSnapshot

VARIABLES
        (* Format - Function from blob ID to set of contents it holds. 
            <<[blob_id |-> <<snap_id, blob_idx_in_snapshot>>, content_ids |-> Set of content ids]>>
            Blob ID is a tuple of snap_id and the blob's index in that snapshot process
        *)
        blobs,
        (* Format - Sequence of index blobs each having a sequence of records which map content IDs to a record with blob ID, deleted flag, and timestamp.
            <<
                <<[content_id |-> 0, blob_id |-> <<snap_id, blob_idx_in_snapshot>>, deleted |-> TRUE/FALSE, timestamp |-> 0]>>
            >>
        *)
        index_blobs,
        (* Format -
            <<
             [failed |-> TRUE/FALSE,
              contents_set |-> Contents which make up the snapshot
              contents_written |-> Contents that have already been considered for writing,
              index_blobs |-> snapshot of index blobs read at the start of snapshotting process,
              index_blob_to_be_flushed |-> index blob that can be flushed to global index_blobs,
              start_timestamp |-> start_timestamp,
              timestamp |-> timestamp,
              blobs_written |-> 0]
            >>
        *)
        snapshots,
        current_timestamp

\*MaxOccurenceBag(set) == [set -> MaxCntOfContentInSnapshot]

KopiaInit == /\ snapshots = <<>>
             /\ current_timestamp = 0
             /\ index_blobs = <<>>
             /\ blobs = <<>>

NonEmptyPowerset(s) == (SUBSET s \ {{}})

PossibleBlobs == Seq([blob_id: (1..MaxSnapshotsIssued) \X (Nat), content_ids: NonEmptyPowerset(0..NumContents-1)])
PossibleIndexBlobs == Seq(
                        Seq([
                            content_id: 0..NumContents-1,
                            blob_id: (1..MaxSnapshotsIssued) \X (Nat),
                            deleted: {TRUE, FALSE},
                            timestamp: 1..(MaxSnapshotTime * MaxSnapshotsIssued)])
                        )

KopiaTypeOK == /\ blobs \in PossibleBlobs
               /\ index_blobs \in PossibleIndexBlobs
               /\ current_timestamp \in 0..(MaxSnapshotTime * MaxSnapshotsIssued)
\*/\ snapshots \in Seq(
\*                    [
\*                        failed: {TRUE, FALSE},
\*                        contents_set: SUBSET 0..NUmContents-1,
\*                        contents_written: 0..NumContent-1,
\*                        index_blobs: Seq])

RECURSIVE SequenceFromSet(_)

SequenceFromSet(s) == IF s = {} THEN <<>>
                      ELSE
                        LET b == CHOOSE a \in s: TRUE
                        IN <<b>> \o SequenceFromSet(s\{b})

HasContentInfo(idx_blobs, content_id) == LET matching_content_infos == UNION({
                                            UNION{
                                                IF idx_blobs[blob_idx][content_idx].content_id = content_id THEN {idx_blobs[blob_idx][content_idx]}
                                                ELSE {} : content_idx \in DOMAIN idx_blobs[blob_idx]} : blob_idx \in DOMAIN idx_blobs})
                                         IN IF matching_content_infos # {} THEN TRUE
                                            ELSE FALSE

\* An index blob will have just one entry for each content ID. It can't have more than one. If this assumption breaks, change this logic.
\* Call only if HasContentInfo is TRUE
GetContentInfo(idx_blobs, content_id) ==
                                        LET matching_content_infos == UNION({
                                            UNION{
                                                IF idx_blobs[blob_idx][content_idx].content_id = content_id THEN {idx_blobs[blob_idx][content_idx]}
                                                ELSE {} : content_idx \in DOMAIN idx_blobs[blob_idx]} : blob_idx \in DOMAIN idx_blobs})
                                        IN CHOOSE content_info \in matching_content_infos:
                                                \A c \in matching_content_infos: c.timestamp <= content_info.timestamp

(* A snapshot can write many contents in one blob.
   Also, the contents can be divided in blobs in any fashion.
   TLC will consider all scenarios *) 
WriteBlob(snap_id) == LET 
                            snap == snapshots[snap_id]
                            blob_id == <<snap_id>> \o <<snap.blobs_written>>
                            timestamp == snap.timestamp
                            start_timestamp == snap.start_timestamp
                      IN /\ \E contents_to_write \in NonEmptyPowerset(snap.contents_set \ snap.contents_written):
                            LET contents_non_existing == {c_id \in contents_to_write:
                                                            (\/ ~ HasContentInfo(snap.index_blobs, c_id)
                                                             \/ GetContentInfo(snap.index_blobs, c_id).deleted)}
                            IN
                             /\ IF contents_non_existing # {} THEN blobs' = Append(blobs, [blob_id |-> blob_id, content_ids |-> contents_non_existing])
                                ELSE blobs' = blobs
                             \* Assuming that there is a difference of atleast 1 time unit between blobs that are written.
                             \* Also assuming all contents in the blob have the same timestamp. Check extent of modelling?
                             /\ \E next_timestamp \in (timestamp+1..(start_timestamp+MaxSnapshotTime)):
                                LET
                                    content_entries_seq == SequenceFromSet(contents_non_existing)
                                    index_blob_entries == [idx \in DOMAIN content_entries_seq |-> [
                                                            content_id |-> content_entries_seq[idx],
                                                            timestamp |-> next_timestamp,
                                                            blob_id |-> blob_id,
                                                            deleted |-> FALSE]]
                                IN /\ snapshots' = [snapshots EXCEPT ![snap_id].timestamp = next_timestamp,
                                                                     ![snap_id].contents_written = snap.contents_written \cup contents_to_write,
                                                                     ![snap_id].index_blob_to_be_flushed = snap.index_blob_to_be_flushed \o index_blob_entries,
                                                                     ![snap_id].blobs_written = snap.blobs_written + 1]
 
FlushIndex(snap_id) == /\ snapshots' = [snapshots EXCEPT ![snap_id].index_blobs = Append(snapshots[snap_id].index_blobs, snapshots[snap_id].index_blob_to_be_flushed),
                                                         ![snap_id].index_blob_to_be_flushed = <<>>]
                       /\ index_blobs' = Append(index_blobs, snapshots[snap_id].index_blob_to_be_flushed)
                       /\ current_timestamp' = IF current_timestamp < snapshots[snap_id].timestamp THEN snapshots[snap_id].timestamp ELSE current_timestamp

TriggerSnapshot(contents_set) == /\ snapshots' = Append(snapshots, [
                                        failed |-> FALSE, contents_set |-> contents_set, contents_written |-> {},
                                        index_blobs |-> index_blobs,
                                        index_blob_to_be_flushed |-> <<>>, timestamp |-> current_timestamp,
                                        blobs_written |-> 0, start_timestamp |-> current_timestamp])
 
KopiaNext == 
             \/ 
                \* Trigger a snapshot
                /\ Len(snapshots) < MaxSnapshotsIssued
                /\ \E contents_set \in NonEmptyPowerset(0..NumContents-1):
                        /\ TriggerSnapshot(contents_set)
                /\ UNCHANGED <<blobs, index_blobs, current_timestamp>>
             \/ 
                /\ \E snap_id \in DOMAIN snapshots:
                    \* Write some contents to a blob
                    \/  /\ snapshots[snap_id].failed = FALSE
                        /\ WriteBlob(snap_id)
                        /\ UNCHANGED <<index_blobs, current_timestamp>>
                    \* Flush index 
                    \/  /\ snapshots[snap_id].failed = FALSE
                        /\ snapshots[snap_id].index_blob_to_be_flushed # <<>>
                        /\ FlushIndex(snap_id)
                        /\ UNCHANGED <<blobs>>
\*                    \* Fail snapshot
\*                    \/  /\ snapshots' = [snapshots EXCEPT ![snap_id].failed = TRUE]
\*                        /\ UNCHANGED <<blobs, index_blobs, current_timestamp>>

RECURSIVE NumberOfContentInfos(_), NumberOfContentsFlushedTotal(_)

NumberOfContentInfos(idx_blobs) == IF idx_blobs = <<>> THEN 0
                                   ELSE Len(Head(idx_blobs)) + NumberOfContentInfos(Tail(idx_blobs))
NumberOfContentsFlushedTotal(snaps) == IF snaps = <<>> THEN 0
                                       ELSE Cardinality(Head(snaps).contents_written) - Len(Head(snaps).index_blob_to_be_flushed) + NumberOfContentsFlushedTotal(Tail(snaps))

TestInv == NumberOfContentInfos(index_blobs) = NumberOfContentsFlushedTotal(snapshots)

=============================================================================
\* Modification History
\* Last modified Fri Apr 10 15:50:37 CDT 2020 by pkj
\* Created Fri Apr 10 15:50:28 CDT 2020 by pkj
