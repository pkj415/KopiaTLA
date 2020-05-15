# Introduction

<div style="text-align: justify">

[Kopia] (https://kopia.io/) is a backup/restore tool which allows creating snapshots of filesystem contents and uploading them to a specified remote cloud storage (it supports S3, GCS, and a few more).

As of commit [9c3d419bc396c0446f21c68813ca195196843eab] (https://github.com/kopia/kopia/tree/9c3d419bc396c0446f21c68813ca195196843eab), Kopia does a periodic garbage collection (abbreviated GC) which is known to break safety conditions (data of a snapshot is deleted even when the snapshot isn't deleted). Let us call this the vanilla garbage collector. The TLA+ specification in the master branch of this repository corresponds to vanilla GC and is written to confirm and identify the behaviour where safety is broken. There is a new design of GC (called GC2) documented here by Julio. The document also explains why vanilla GC breaks safety (I will explain it here as well). The specification in gc2 branch corresponds to the "GC with metadata" design as presented in the document. However, GC2 doesn't guarantee safety either and the specification for gc2 demonstrates this. This page also explains the various optimizations and tricks used to abstract out relevant part of the implementation to be specified.

The architecture of Kopia is explained well [here] (https://kopia.io/docs/architecture/). I will explain the important pieces to keep in mind for our purposes of specifying behaviours relevant to GC in Kopia.

# Abstraction

This section presents an initial abstraction of the entities and interactions between them as seen in Kopia. This initial abstraction represents a starting point I used based on reading the architecture document and code. Later sections show some techniques used to further simplify/modify the abstraction such that the techniques can be generalized to other specifications.

Kopia stores its data in a data structure called *Repository*. It encompasses a lot of features to efficiently create snapshots and maintain them.

The atomic unit of data in a repository is called a *content* (each content has a unique content id which is a deterministic hash of the content data). A bunch of contents (or a bunch of index entries that point to the contents; explained more shortly) are stored together in a *blob*. Contents are stored in *data blobs* and index entries are stored in *index blobs*. Each blob has a randomly generated blob id. A new blob can be written to the repository as a whole, but not partially. Once written a blob can't be modified. When a process writes some contents, they are are packed into a *data blob* and the data blob is written once some threshold for the size of a blob is crossed. Alongside writing contents to the repository in batches of approximately blob size, *index blobs*, which contain information about how to find data corresponding to content ids, are written (might be called flushed at places) periodically. Each index blob is a set of entries of the form - content id of newly written content, the blob id and offset in the blob to which the content was written, timestamp of when the content was written and a flag to indiciate if this marks content for a content id as deleted (more on how this flag works shortly). Index blobs are flushed periodicially. Each index blob usually contains entries for contents from multiple blobs written since the last index flush.

Tieing it all up, a repository contains index blobs and data blobs. The data blobs contain contents which are referenced by entries in the index blobs.

Also keep in mind that in all figures the content id (such as C4) is some hash of the content data that is written in the content. If two processes write the same content (i.e., those having same data) to the repository, they will write index entries with the same content id.

![](Image 1.tif "Organization of contents, index blobs and data blobs")

### Processes in Kopia

Only two processes concern us - snapshot processing and garbage collection.

#### Snapshot processing

The process to create a snapshot in Kopia writes file data to a repository after splitting into objects and inturn each object is split into contents. We can ignore this detail and assume that a snapshot process starts up with the intention to write a set of contents (and the corresponding index entries to find those contents) to the repository. The contents are written in data blobs and index entries are periodically flushed, one index blob at a time.

When a process to create a snapshot is triggered, it reads a point in time copy of the set of index blobs on start up before performing any tasks and stores all the index entries in an unordered set (the information about division of index entries in different index blobs is lost and is not needed). This local copy of index entries helps in deduplication of data i.e., if some data has already been written to the repository, the snapshotting process can avoid writing the data again. This is done by checking if there exists an index entry for the content id (which is a hash of the content data which the snapshotting process intends to write). Note that only those contents are visible to the snapshotting process which were flushed before a point in time view of the index blobs was stored in the local index entries set of the snapshotting process. To search any content, a process searches its local set of index entries to find the entry with the latest timestamp for the content id being searched (the older index entries for a given content id could also be used but they aren't because in case the latest entry has the delete flag as True, it implies that the content has already been marked for deletion by the GC process and the snapshot should rewrite the content).

As part of snapshotting, when data blobs are written to the repository, they are added to the global set of blobs maintained in the repository. When index blobs are flushed, they are added to the global set of index blobs of the repository. They are also added to the local set of index entries which were populated on startup so that the process can search for the contents it had already written and reuse them.

Completion of a snapshot results in some metadata entry added atomically to the repository which points to the content ids which make up the snapshot.

A snapshot process can complete within a time limit as specified by the MaxSnapshotTime constant. On completion, the snapshot metadata is written to the repository atomically (in some way which is unimportant to us). The snapshot can also later be deleted. In case a snapshot process doesn't complete within the time limit, it can still write contents and flush indices to the repository. However, it cannot mark itself completed (i.e., the snapshot metadata can't be written).

Deletion of a snapshot results in the metadata entry of the snapshot being deleted. In this specification this is just modeled by marking the deleted flag in the snapshot record as True.

The following image slide shows a starting state of the repository with no data blobs and no index blobs. There are two snapshots which are started one after the other. The first snapshot process S1 intends to write some contents {C45, C46, C47} and the process starts at timestamp 10. So it keeps a local view of the index entries in the repository as of time 10. It write contents C45 and C46 in one data blob and flushes the index entries for those in an index blob. Later another snapshot process S2 which intends to write the contents {C45, C46, C47, C48} is triggered at timestamp 12 and it reads a point in time view of index entries as of timestamp 12. It find contents C45 and C46 already in the local index entries set. However, after this the first snapshot process S1 writes content C47, flushes the index and marks itself completed. But S2 isn't aware of this as the local set of index entries are populated only at the start of snapshotting process. So the content C47 is written again. Note that now there will be two index entries for the same content, one being the latest one. All later processes which read contents will rely only on the latest index entry and so any earlier index entries and their corresponding content data in the data blob are useless. Also, post this snapshot S2 is deleted and so content C48 is useless as well. It is the task of the garbage collection module (in conjunction with index compaction and blob compation) to delete any unused contents & corresponding index entries and free space.

#### Garbage collection, index compaction and blob compaction

**Content removed due to index blob compaction after being marked deleted by garbage collection** - From the previous example of snapshotting, the content C48 is not referenced by any snapshot. This will be cleaned by being marked as deleted by the GC process which sweeps through metadata of all snapshots to find contents which are referenced by any snapshot and the sweeps through a point in time view of the global set of index blobs to find index entries of content ids which are are not referenced by any snapshot. Marking a content as deleted only involves adding an index entry for the content id with the deleted flag as True and a timestamp. Later the index compaction process will remove all the index entries for C48. Post this blob compaction will remove all contents which are not referenced by an index entry. You might have guessed what might be wrong here - there might exist a snapshot process that started before the GC process. which read the global set of index blobs to create its local set of index entries and then reused the content. This is an issue because if later we try to read the snapshot, the content id might not be found using any index entry as it would have been removed by index compaction. Note that before index compaction, we can still find the content data by looking for index entries before the index entry with the deleted marker set to True.

**Content removed due to data blob compaction without garbage collection process' intervention** - If you notice, the content C47 is present twice in the blob store and has two index entries. The older index entry and it's corresponding content data in are not required and can be removed. The older entry will be cleaned up by index compaction and its corresponding content will be cleaned up by blob compaction. This presents no issue as any snapshot metadata which is written will contain just the content ids which it is made of and the new index entry can be used to search for it. It doesn't matter if during the snapshot process, the content was found at another location using some old index entry.

##### How index blob compaction works -

If there are index entries for contents which are marked deleted (i.e., the latest index entry for the content id is marked deleted) then all index entries (including earlier ones) for the content can be deleted. If there are multiple index entries for undeleted contents, the older ones can be removed. In case there exist two index entries for a content with the same timestamp (this can happen in case two snapshot processes independently write the content at the same time), either of the index entries can be removed.

Since blobs can't be modified in Kopia, index compaction of a set of index blobs X involves creating a new index blob without index entries which are to be removed from the entries in X. Once the new index blob is created, the set of index blobs X can be deleted. The removal is done post creation of the new index so that no content specified in stored snapshots become unreachable.

##### How data blob compaction works -

Blob compaction sweeps through all contents in all blobs in the repository and deletes any contents which are not referenced by any index entry in the index blobs. Deleted contents can't be removed by shifting contents in a blob as a blob is immutable. The only way to compact blobs is to find blobs which contain contents which are no longer needed (i.e., not referenced by any index entry) and then merge them into a smaller number of blobs without the deleted contents. Also, a new set of indices will have to be written to point to the new contents. Post this, the old blobs can be removed. Note that after writing new index blobs, there will be old entries for many contents in the old index blobs and this will be taken care of my index compaction.

Based on this basic abstraction of the the entities involved and the processes, it seems fair to define the following data structures for state variables in the specification -

```
(*  Bag of index blobs. Element in the bag is an index blob. The blob ID is not shown as it is irrelevent.
    Each index blob is a set of content entries. This is a set because once a content is added to a blob for
    writing, it will not be added again for writing again by the same snapshot process.

    Note that we use a bag of index blobs because two processes might write the same index blob (differentiated
    by the blob id in the implementation).

    {
        {content_id |-> 0, deleted |-> TRUE/FALSE, timestamp |-> 0}
    }
*)
index_blobs,

(* Bag of records where each record represents a snapshot process while it is in progress. If there is a record with status as completed,
   it is as good as a representation of snapshot metadata in the repo with its content ids found in the contents_to_be_written field.
    {
     [status |-> "in_progress", "completed", "deleted", \* "completed" is analogous to the manifest for the snapshot being written to the store
      contents_to_be_written |-> content ids of contents that have to be written to the blob storage for the snapshot to be marked complete,
      local_index_entries |-> point in time view of index read at the start of snapshotting process, later this is updated on every
        flush of indices. Note that the update will only append flushed indices to this field. The indices are not refreshed from
        the global indices,
      index_blob_to_be_flushed |-> next index blob with contents that haven't been flushed to the global bag of index_blobs and
      that can be flushed to global index; once flushed, this will be reset to empty set,
      start_timestamp |-> start_timestamp]
    }
*)
snapshots,

(* Bag of records where each record represents a garbage collection process.
    {
        [
            local_snapshot_entries |-> point in time view of snapshots (i.e., completed snapshot processes) in the repository. Populated when this GC is triggered,
            local_index_entries |-> set representing a point in time view of the global bag of index blobs,
            contents_deleted |-> set of deleted content ids to keep track of the content ids which are already marked deleted in some step earlier,
            deletions_to_be_flushed |-> next index blob of deletion entries that can be flushed to global index. Once flushed this will be reset to empty set
        ]
    }
*)
gcs
```

### Abstracting out relevant parts

#### Ignore data blobs and data blob compaction

We have already started with a very minimal representation of a repository and a snapshot process. But we will now go further.

The TLA+ spec ignores blobs and a state only maintains the set of index blobs (actually in a more simpler way - just a set of index entries without capturing the fact that indicies are batch stored in blobs because all processes populate all index entries present in different blobs in a single data structure). We can ignore blobs because a blob is meaningful (i.e., seen by other processes) only if the corresponding index blob which references to contents in the blob is flushed. Also, as we saw, safety is broken just after a content referenced by some snapshot is no longer available in the global set of index blobs. Blob compaction occurs after that and if safety was broken before blob compaction, there is nothing that blob compaction will change (i.e., safety will stay broken). Also, just blob compaction will never result in violation of safety as only those contents are removed which can no longer be referenced by any index entries or correspond to an index entry for a content marked deleted. If a process which references a content can't find the index entry for it, safety is broken. It can't find the blob irrepective of blob compaction occured or not.

In a nut shell, it can't happen that an index entry was referencing a content in some blob and that content got deleted because of blob compaction. And so, we don't have to consider blobs and blob compaction in our specification. Just index entries suffice.

Also, given we are ignoring blobs, the content entries in the global index set doesn't include references to blob ids (if the index entry exists and is latest, the blob will surely exist. And if the index entry is not the latest for a given content id, the blob is allowed to not exist without violating safety and the latest index entry will surely point to a blob with the content).

#### Choose data structures of state variables wisely

The index entries are stored together as a set instead of separate blobs because - when a process starts up it populates data from all index blobs into a single data structure. It doesn't matter if the index entries {A, B, C, D} were written earlier as blobs {A, B} and {C, D} or as blobs {A} and {B, C, D} or in any other manner. The resulting state is semantically the same and how the index entries are split in chunks doesn't matter. (Note that how the index entries are split in chunks does matter during index compaction as whole index blobs are deleted atomically, but we will see that not having index blobs allows more behaviours than possible by the actual implementation).

Also note that in the figure with two snapshot processes writing contents to the repository, if they write the same content with the same timestamp, there would exist two content entries for the same content in two index blobs pointing to different copies of the content in different data blobs. However, a state with these two content entries is semantically equiavlent to a state with just one of those index entries. And so, we don't use a bag of contents, but a set of contents. However, if a content is written two times at different timestamps, it will occur twice in the set as the timestamp will be a differentiator for the index entries.

Image to show this

For snapshots, a bag is used because there might be two snapshot processes with exactly the same start timestamp, contents written, and values for other fields. Earlier I had used a sequence instead of a bag to allow duplicates and that was an overkill.

Use unordered data structures such as bags and sets where ever possible (if different orderings of the elements result in semantically same states) instead of sequences to reduce the state space.

#### Avoiding semantically same distinct states

I will usually call two states in TLA+ to be semantically equivalent and that only means that - the states might differ in some variable(s) and no temporal properties to be checked and sequence of steps that follow depend on this difference in values of the variables.
