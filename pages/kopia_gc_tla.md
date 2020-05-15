---
layout: page
title: TLA+ for Kopia

images:
  - image: {{ BASE_PATH }}/assets/images/Img.002.png
  - image: {{ BASE_PATH }}/assets/images/Img.003.png
  - image: {{ BASE_PATH }}/assets/images/Img.004.png
  - image: {{ BASE_PATH }}/assets/images/Img.005.png
  - image: {{ BASE_PATH }}/assets/images/Img.006.png
  - image: {{ BASE_PATH }}/assets/images/Img.007.png
  - image: {{ BASE_PATH }}/assets/images/Img.008.png
  - image: {{ BASE_PATH }}/assets/images/Img.009.png
  - image: {{ BASE_PATH }}/assets/images/Img.010.png
  - image: {{ BASE_PATH }}/assets/images/Img.011.png
  - image: {{ BASE_PATH }}/assets/images/Img.012.png
  - image: {{ BASE_PATH }}/assets/images/Img.013.png
  - image: {{ BASE_PATH }}/assets/images/Img.014.png
  - image: {{ BASE_PATH }}/assets/images/Img.015.png
  - image: {{ BASE_PATH }}/assets/images/Img.016.png
  - image: {{ BASE_PATH }}/assets/images/Img.017.png
  - image: {{ BASE_PATH }}/assets/images/Img.018.png
  - image: {{ BASE_PATH }}/assets/images/Img.019.png
  - image: {{ BASE_PATH }}/assets/images/Img.020.png
  - image: {{ BASE_PATH }}/assets/images/Img.021.png
---

Apart from this, there is a snapshot and backup tool - Kopia. The garbage collector module in Kopia was known to have correctness issues and there is a new design proposed by Julio and Jarek to solve this issue. However, the new design also violates correctness guarantees and I describe that work here.

The pages explain the optimizations and tricks used to specify the protocols. It might require some knowledge of TLA+, but I hope with the short brief above is enough to understand the techniques used.

[Kopia](https://kopia.io/) is a backup/restore tool which allows creating snapshots of filesystem contents and uploading them to some specified remote cloud storage (it supports S3, GCS, and a few more).

As of [this commit](https://github.com/kopia/kopia/tree/9c3d419bc396c0446f21c68813ca195196843eab), Kopia does periodic garbage collection (abbreviated GC) to free up data corresponding to deleted snapshots which is known to break safety conditions (data of a snapshot is deleted even when the snapshot isn't deleted). Let us call the strategy of garbage collection followed in the specified commit as vanilla garbage collection. The TLA+ specification in the master branch of this repository corresponds to vanilla GC and is written to confirm and identify the behaviour where safety is broken. There is a new design of GC (called GC2) documented here by Julio. The document also explains why vanilla GC breaks safety (I will explain it here as well). The specification in gc2 branch corresponds to the "GC with metadata" design as presented in the GC2 design document. However, GC2 doesn't guarantee safety either and the specification for gc2 demonstrates this. This page also explains the various optimizations and tricks used to abstract out relevant parts of the implementation to be specified.

The architecture of Kopia is explained well [here](https://kopia.io/docs/architecture/). I will explain the important pieces to keep in mind for our purposes of specifying behaviours relevant to GC in Kopia.


# Abstraction for vanilla GC

This section presents an initial abstraction of the entities and interactions between them as seen in Kopia. This initial abstraction represents a starting point I used based on reading the architecture document and code. Later sections explain some techniques used to further simplify/modify the abstraction and they are general enough to be used in specifications for other systems.

Kopia stores its data in a data structure called *Repository*. The atomic unit of data in a repository is called a *content* (each content has a unique content id which is a deterministic hash of the content data). A bunch of contents (or a bunch of index entries that point to the contents; explained more shortly) are stored together in a *blob*. Contents are stored in *data blobs* and index entries are stored in *index blobs*. Each blob has a randomly generated blob id. A new blob can be written to the repository as a whole, but not partially. Once written, a blob can't be modified. When a snapshotting process writes some contents, they are are packed (i.e., appended) over time into a local *data blob* and the data blob is written (to the repository which is usually located in some cloud storage) once some threshold for the size of the local data blob is crossed. Alongside writing contents to the repository in batches of approximately blob size, *index blobs*, which contain information about how to find data corresponding to content ids, are written to the repository. When contents are packed into data blobs, correponding index entries (with information about where to find the content later) are packed in a local index blob which is written/flushed periodically to the repository. Each index blob is a set of entries of the form - content id of newly written content, the blob id and offset in the blob to which the content was written, timestamp of when the content was written and a flag to indiciate if this marks the content for a content id as deleted (more on how this flag works shortly). Index blobs are flushed periodicially. Each index blob usually contains entries for contents from multiple data blobs which have been written to the repository since the last index blob flush. At a time there exists only one local index and data blob waiting to be written to the remote repository.

Tieing it all up, a repository contains index blobs and data blobs. The data blobs contain contents which are referenced by entries in the index blobs. Keep in mind that in all figures, the content id (such as C4) is some hash of the content data that is written in the content. The content id provides content-addresability i.e., any snapshot process can reuse the content already written earlier (perhaps by another snapshot process) by searching for the content data to be written using the hash of the content data. All index entries for a data blob will be found in the same index blob. Below is a sample depiction of three data blobs and 2 index blobs in a repository.

![]({{ BASE_PATH }}/assets/images/index_and_data_blobs.png "Organization of contents, index blobs and data blobs")

## Processes in Kopia

Only two processes concern us - snapshot creation and garbage collection.

#### Snapshot creation

The process of snapshot creation in Kopia writes filesystem data (under a user specified root directory) to a repository after splitting the data into objects, where each object is inturn  split into contents. We can ignore this detail and assume that a snapshot process starts up with the intention to write a set of contents (and the corresponding index entries to find those contents) to the repository. The contents are written in data blobs and index entries are periodically flushed, one index blob at a time.

When a process to create a snapshot is triggered, it reads a point in time copy of the index blobs on start up before performing any tasks and stores all the index entries from all index blobs in an unordered set (the information about division of index entries into different index blobs and ordering of index entries in each blob is not needed and hence is not maintained in the local copy of index entries). This local copy of index entries helps in deduplication of data i.e., if some data has already been written to the repository, the snapshotting process can avoid writing the data again (also called reusing the content). This is done by checking if there exists an index entry for the content id (which is a hash of the content data which the snapshotting process intends to write). Note that only those contents are visible to the snapshotting process which were flushed before a point in time view of the index blobs was stored in the local index entries set of the snapshotting process. To search any content, a process searches its local set of index entries to find the entry with the latest timestamp for the content id being searched (the older index entries for a given content id could also be used but they aren't because - in case the latest entry has the delete flag set as True, it implies that the content has already been marked for deletion by the GC process and the snapshot should rewrite the content; this will become more clear in the GC process section).

As part of snapshotting, when data blobs are written to the repository, they are added to the global list of blobs maintained in the repository. When index blobs are flushed, they are added to the global list of index blobs of the repository. They are also added to the local set of index entries which were populated on startup so that the process can search for the contents it had already written and reuse them.

Completion of a snapshot results in some metadata entry added atomically to the repository which points to the content ids which make up the snapshot. A snapshot process can complete within a time limit as specified by the MaxSnapshotTime constant. On completion, the snapshot metadata is written to the repository atomically (in some way which is unimportant to us). In case a snapshot process doesn't complete within the time limit, it can still write contents and flush indices to the repository. However, it cannot mark itself completed (i.e., the snapshot metadata can't be written).

**NOTE -** When we say snapshot in this document later, we mean the snapshot metadata which defines it. Without snapshot metadata written in the repository, the snapshot doesn't exist for the outside world even if a snapshot creation process has written all the data to the repository but failed just before writing the snapshot metadata to the repository.

A snapshot can also later be deleted. Deletion of a snapshot results in the metadata entry of the snapshot being deleted.

The following image slide shows a starting state of the repository with no data blobs and no index blobs. There are two snapshot creation processess which are started one after the other. The first snapshot process S1 intends to write some contents {C45, C46, C47} and the process starts at timestamp 0. It writes one data blob with contents C45 & C46 and writes in an index blob with the corresponding index entries. Later another snapshot process S2 which intends to write the contents {C45, C46, C47, C48} is triggered and it reads a point in time view of index entries from the index blob. It finds contents C45 & C46 already in the local index entries set and so doesn't add them to the local data blob for writing. However, after this the first snapshot process S1 writes another data blob with content C47, flushes the index blob and marks itself completed. But S2 isn't aware of this new index entry as the local set of index entries are populated only at the start of snapshotting process. So it writes a data blob with the content C47 & C48. C47 is now present in two data blobs with two different index entries in separate index blobs pointing to the respective data blob contents. Having two copies of the same content just consumes space and is useless. Post this snapshot S2 is deleted and so content C48 is useless as well. It is the task of the garbage collection module (in conjunction with index compaction and blob compation) to delete any unused contents & corresponding index entries to free space.

{% include carousel.html height="50" unit="%" duration="7" %}

#### Garbage collection, index compaction and blob compaction

Garbage collection of unused contents (either due to duplicate copies of a content or due to the fact that no snapshot metadata refers to a content) in Kopia is not trivial. This is due two reasons -

1. Blobs are immutable which requires GC to rewrite them without the contents (or index entries) which are not needed anymore followed by deletion of the old blobs.
2. Even as we rewrite blobs while keeping only necessary information, it might happen that another snapshot process which started simultaneously with the garbage collection  process, reuses a content while it is being considered for deletetion.

The strategy of vanilla garbage collection in Kopia is described next for both cases when a content is not needed anymore -

1. Duplicate copies of the content exist and all except one copy can be removed.
2. The content is not being referenced by any snapshot.

**Content with duplicate copies** - In this case, the content is removed in two stages - i. index blob compaction ii. data blob compaction. This is without garbage collection process' intervention. If you notice, the content C47 is present twice in the blob store and has two index entries. The older index entry and it's corresponding content data are removed. The older entry will be cleaned up by index compaction and its corresponding content will be cleaned up by data blob compaction. This presents no issue as restoration of any snapshot which references the content will remain unhindered as a copy of the content is still present which can be referenced using the index entry which is left untouched. Both index and data blob compaction are periodically scheduled background tasks and they are explained in more detail later.

**Content not referenced by an snapshot** - In this case, the content is removed in three stages - i. content is marked deleted by the GC process (more on what "marking" deleted means shortly) ii. all index entries for the content are removed by index blob compaction iii. the actual content is deleted via data blob compaction. From the previous example of snapshotting, the content C48 is not referenced by any snapshot metadata. This will be cleaned by being marked as deleted by the GC process which first collects a point in time view of snapshots and list of index blobs. It then sweeps through all snapshots to find content IDs which are referenced by any snapshot and then sweeps through the list of index blobs to find index entries of content ids which are are not referenced by any snapshots. Marking a content as deleted involves adding an index entry for the content id with the deleted flag as True and a timestamp. Later, the next scheduled index compaction process will remove all the index entries for C48 including and older than the deleted entry. Post this blob compaction will remove all contents which are not referenced by an index entry. Also, to avoid cases where GC marks content written by a snapshot creation process in progress as deleted, GC ensures that it marks contents which are older than MaxSnapshotTime.

In a nutshell, any content which is no longer referenced by a snapshot is marked deleted by GC so that its index entries can later be removed completely by index compaction and content data can later be removed completely by blob compaction similar to the previous case of cleaning up duplicate contents. The delete marker is just an indication that not even a single copy of the content before the deleted entry timestamp is to be kept in the system. And any later snapshot creation is expected to rewrite the content (the GC can't retain the content because it can't anticipate when such a snapshot creation will occur and keeping the content around for this possibility is just a waste of space. It is beneficial to rewrite the content later instead of wasting space to possibly avoid writing the content later).

You might have guessed what might be wrong here - there might exist a snapshot process that started before the GC process. which read the global list of index blobs to create its local set of index entries and then reused the content. This is an issue because if later we try to read the snapshot (possibly for restoring it), the content might not be found via any index entry as it would have been removed by index compaction (the GC running in parallel with the snapshot would have marked the content deleted). Note that before index compaction, we can still find the content data by looking for index entries before the index entry with the deleted marker set to True. But this is only if we get lucky that the scheduled index compaction process doesn't delete the index entries before we read the snapshot. Also, even if we get lucky, eventually index compaction will remove the index entries and we will not be able to read all contents of the snapshot later.

##### How index blob compaction works -

If there is an index entry for a content that marks it deleted then all earlier index entries for the content (including the one that marks it deleted) can be removed. If there are multiple index entries for undeleted contents, the older ones can be removed. In case there exist two index entries for a content with the same timestamp (this can happen in case two snapshot processes independently write the content at the same time), either of the index entries can be removed.

Since blobs are immutable in Kopia, index compaction of a list of index blobs X involves creating a new index blob without index entries which are to be removed from the entries in X. Once the new index blob is created, the index blobs in X can be deleted. The removal is done post flushing of the new index blob so that no content specified in snapshots becomes unreachable.

##### How data blob compaction works -

Blob compaction sweeps through all contents in all data blobs in the repository and deletes any contents which are not referenced by any index entry in the index blobs. Contents can't be removed by shifting contents in a data blob as a blob is immutable. The only way to compact blobs is to find blobs which contain contents which are no longer needed (i.e., not referenced by any index entry) and then merge them into a smaller number of blobs without the unneeded contents. Also, a new set of indices will have to be written to point to the new contents. Post this, the old data blobs can be removed. Note that after writing new index blobs, there will be duplicate old entries for many contents in the old index blobs and this will be taken care of by index compaction.

### State variables based on initial abstraction

Based on the basic abstraction of the the entities involved and the processes, we can start with an initial choice of data structures for the state variables and the steps of the spec. We will refine the state variables and steps as we go along. Note that I will show the refinement in state variables explicitly but will not show what the steps look like syntactically in each refinement of the specification. I will explain in plain english what each step does and when it is enabled. This will help keep the focus on important parts without getting lost in the syntactic details of the specification.

To start off, we have the following state variables in the specification (every state variable name has the type as the suffix in case it is a set/bag/list/record). Bags and lists (also called sequences) can have duplicate elements.  Records are just a mapping from field names to values.

1. data\_blobs\_list - a list of data blobs. Each data blob in the list has -
	* blob\_id - a blob ID (required so that any index entry and reference it)
	* content\_ids\_list - a list of content IDs (we represent only content IDs because the actual data is not relevant to the specification)

2. index\_blobs\_list - A list of index blobs. Each index blob in the list has -
	* index\_entries\_list - a list of index entries with each entry having - the content id, the deleted flag, timestamp and the location of the content (just the data blob id is enough as the offset doesn't matter to the specification i.e., if a data blob with the blob id exists, whatever be the offset, the content will be found. This is because the data blob either exists fully or not at all)

		We don't need to bother about index blob ids as they serve no purpose in any step.

3. snapshot\_processes\_bag - a bag of snapshot creation processes. Each snapshot creation process has -
	* status - if it is "in_progress", "completed" or "deleted". Note that we don't separately have a state variable for snapshots. They are just represented by snapshot processes which have status "completed". This is done just for syntactic simplicity of the specification.
   * content\_ids\_to\_be\_written\_list - a list of content ids of contents that the snapshot process will write in the same order and post which it can be marked complete.
   * local\_index\_entries\_set - a set populated from the point in time view of list of index blobs read at the start of snapshotting process (TriggerSnapshot step), later this is updated on every flush of index blob by the snapshot. Note that we use a set as the division and ordering of the content IDs in index blobs doens't matter to snapshot creation processes
   * local\_data\_blob\_record - has the same format as a data blob except the blob\_id
   * local\_index\_blob\_list - a list of index entries represetning the next index blob with contents that haven't been flushed to the global list of index_blobs; once flushed, this will be reset to empty set.
   * start_timestamp - start time of the snapshot creation process.

4. gc\_processes\_bag - a bag of GC processes. Each GC process has -
	* local\_snapshot\_entries\_bag - a bag representing point in time view of snapshots (i.e., completed snapshot processes) in the repository. Populated when the GC process is triggered.
    * local\_index\_blobs\_list - a point in time copy of the list of index blobs read when GC process is triggered, later this
         is updated on every flush of the local\_index\_blob\_list (with entries of contents marked deleted),
	* local\_index\_blob\_list - a list of index entries representing the next index blob of deletion entries that can be flushed to global list of index blobs. Once flushed this will be reset to empty set

5. data\_blob\_compaction\_processes\_bag - a bag of data blob compaction processes with each element having -
	* local\_data\_blobs\_list - a point in time copy of the list of data blobs read when this process is triggered
	* local\_index\_blobs\_set - a set representing a point in time copy of the list of data index blobs read when this process is triggered. Note that we use a set as the division and ordering of the content IDs in index blobs doens't matter to data blob compaction
	* local\_data\_blob\_record - has the same format as a data blob except the blob\_id. It represents the local data blob to which contents are packed waiting to be flushed in one go as a blob
	* local\_index\_blob\_list - a list of index entries representing the local index blob which is flushed periodicially similar to as done in a snapshot process
	* current\_blob\_content\_pointer - data blob compaction reads contents from data blobs in order and flushed new data and index blobs similar to snapshot creation. So, we need a pointer to denote which contents are already written either to the local data blob/ or flushed so that the step to write more contents knows where it left of earlier. The pointer will be a tuple of two values - the blob id in the local list of data blobs and the content id in the list of contents in that blob.

6. index\_blob\_compaction\_processes\_bag - a bag of index blob compaction processes with each element having -
   * local\_index\_blobs\_list - a point in time copy of the list of index blobs read when this process is triggered
   * local\_index\_blob\_list - a list of index entries representing the merged index blob. Index compaction results in a single flush of one large index blob and so doesn't need a pointer (as needed in data blob compaction process) to keep track of which index blobs it read and flushed as a new index blob so far from the local\_index\_blobs\_list.

7. logical\_timestamp - a monotonically increasing counter starting from 1
8. next\_blob\_id - a monotonically increasing counter which can be used by snapshot processing to assign a blob id so that two snapshots don't assign the same blob id.

A bag is used for the processes because there might be two processes of the same type running simulatenously with the same local state. For example, two snapshot processes running simulatneously might have started with the intention to write the same set of contents and might have as of some state in the behaviour written the same set of index & data blobs and have the same values for local state of the processes.

We use a couple of contraints to restrict the number of behaviours that TLC captured. In other words, content IDs in the actual implementation might be a 16-bit value say allowing 2^16 content IDs, but we surely don't want to run TLC to capture all behaviours with these content IDs. Also, it isn't feasible. For this, we keep only a set of possible content IDs in our world, say {1, 2, 3}.

We use the following constant to restrict the set of behaviours captured -
1. NumContentIDs - content IDs from 0 to NumContents-1 are allowed.
2. NumSnapshots - Maximum number of total snapshot process records in the system i.e., no more than NumSnapshots snapshot processes can be triggered
3. NumGCs - Maximum number of total GC process records in the system
4. NumDataBlobCompactions
5. NumIndexBlobCompactions
6. MaxLogicalTime - We don't want to allow a behaviour where only the logical timestamp keeps incrementing without any other step being taken ever. So, we restrict the maximum allowed time stamp in the system.

Apart from this, we have one other constant - MaxSnapshotTime. This is the time within which a snapshot process can complete. If it doesn't it can never complete to generate a snapshot metadata entry (i.e., a snapshot).

Let's know discuss the final peice, the steps we need to have in the specification -

1. Tick time forward - just increment the logical\_timestamp. This step is always enabled i.e., has no preconditions.
2. For snapshot processing -
   1. Trigger a new snapshot process -
   	   * Precondition - max limit hasn't been reached.
   	   * Action - Pick a permutation of a subset of content IDs. These are the contents that the snapshot intends to write. Add the snapshot process record to the bag of snapshot processes
   2. WriteContents -
      * Precondition - snapshot hasn't yet written all contents it was supposed to write.
      * Action - Choose some contents to be written in the same timestamp starting at the content ID where it left of last time. This involves adding contents to the local\_data\_blob\_list and the local\_index\_blob\_list.
   3. Flush Index -
   	   * Precondition - local\_data\_blob\_list is empty and local\_index\_blob\_list is not empty
   	   * Action - Append the local\_index\_blob\_list blob to the global index\_blob\_list if the local\_data\_blob\_list is empty (so that index blob is flushed only for all contents already flushed to the repository).
   4. Mark complete -
   	   * Precondition - all contents have been written with the timelimit
   	   * Action - mark the status of the snapshot as complete
   5. Delete snapshot -
      * Precondition - snapshot is in complete status
      * Action - change status to deleted
3. For garbage collection processing -
	1. Trigger a new GC process -
	   * Precondition - max limit of GCs process hasn't been reached.
	   * Action - add a gc process record to the global bag. The process will have a point in time view of the completed snapshot processes and index blobs.
4. For index blob compaction processing -
5. For data blob compaction processing -

Note that we don't have a "failed" state for any snapshot process. In the actual implementation, any snapshot that has not completed within its timelimit can stay in progress for anytime after the timelimit and still write contents, or it can fail. But we haven't explicitly specified a step to fail the snapshot because we will still captures behaviour where a snapshot in progress after the timelimit never takes a step to write any content and this is as good as a failed snapshot process.

Below is a brief representation of our state variables and steps. I have given a sample for each state variable (this syntax is not stricly follwing TLA+ syntax rules, I am just trying to represent everything succinctly). \<\< \>\> is notation to represent a list. Sets and bags are both representated with {} (bags also have a number alongside the element). Records are of the form \[field1 \|-\> value, field2 \|-\> value ...]

```
data_blobs_list,
(* <<
		[blob_id |-> 0, content_ids_list |-> <<0, 1, 2>>],
		[blob_id |-> 1, content_ids_list |-> <<3, 1, 5>>]
	>>
*)

index_blobs_list,
(*  <<
    	<<[content_id |-> 0, deleted |-> TRUE/FALSE, timestamp |-> 0, location |-> 0],
    	  [content_id |-> 1, deleted |-> TRUE/FALSE, timestamp |-> 0, location |-> 1]>>,

    	<<[content_id |-> 4, deleted |-> TRUE/FALSE, timestamp |-> 0, location |-> 2]>>
    >>
*)

snapshot_processess_bag,
(* 
    {
     [status |-> "in_progress",
      content_ids_to_be_written_list |-> <<5, 6, 7, 8, 9>>
      local_index_entries_set |-> {[content_id |-> 4, deleted |-> FALSE, timestamp |-> 0, location |-> 2], ...}
      local_data_blob_record |-> [content_ids_list |-> << 5, 6, 7>>],
      local_index_blob_list |-> <<[content_id |-> 5, deleted |-> FALSE, timestamp |-> 0, location |-> 3], ..>>
      start_timestamp |-> start_timestamp]: 2,
      ...
    }
*)

gcs_processes_bag,
(* {
        [local_snapshot_entries_bag |-> a bag of snapshot processes as above
         local_index_blobs_list |-> ...
         local_index_blob_list |-> ...
        ]: 2,
        ...
    }
*)

index_blob_compaction_processes_bag,
(* {
        [local_index_blobs_list |-> ...
         local_index_blob_list |-> ...
        ]: 2,
        ...
    }
*)

data_blob_compaction_processes_bag,
(* {
        [local_data_blobs_list |-> ...,
         local_index_blobs_set |-> ...,
         local_data_blob_record |-> ...,
         local_index_blob_list |-> ...,     
        ]: 2,
        ...
    }
*)
  
logical_timestamp

Steps -

1. Tick Time forward
2. Trigger a new snapshot process
3. Write contents as part of a snapshot process to local data blob and local index blob
4. Flush local data blob
4. Flush local index blob
5. Mark snapshot process complete
6. Delete snapshot
6. Trigger a new GC process
7. Add some content entries with deleted flag as True at the same timestamp to the local index blob
8. Flush local index blob
9. Trigger index blob compaction process
10. Write new merged index blob
11. Delete a subset of the old index blobs at the same timestamp from the set of index blobs to be deleted (those which have been compacted)
12. Trigger data blob compaction process
13. Write some contents to local data blob and local index blob and move pointer ahead
14. Flush local data blob
15. Flush local index blob
16. Delete old unneeded data blobs (this is only post all new data blobs have been written)
```

### Abstracting out relevant parts

#### Ignore data blobs and data blob compaction

We have already started with a very minimal representation of a repository and the various processes. But we will now go further.

**Safety condition** - Content data for every content id present in a snapshot in the repository can be found.

The state in the spec can ignore the list of data blobs and only maintain the list of index blobs. Safety is violated when content for a content id present in some snapshot is no longer found in the repository. This can happen if the global list of index blobs doesn't contain an index entry to find the content or if the index contains an entry for the content id but the referenced data blob doesn't contain the content or doesn't exist. We know that that the later scenario is not an issue because blob compaction doesn't delete a content from a blob until the corresponding index entry referencing it is not present in the repository.

In a nut shell, it can't happen that an index entry was referencing a content in some data blob and that content got deleted because of data blob compaction. And so, we don't have to consider data blobs and data blob compaction in our specification. Just index blobs and their interaction with snapshot, gc and index blob compaction processes suffice. We know that safety can be violated in Kopia only in a scenario where index blob compaction occurs after gc (with the right edge case where a snapshot running simultaneously with GC referenced the content). Data blob compaction is not the culprit.

**Refined safety condition** - For every content id present in a snapshot in the repository, an index entry with location of content data can be found.

Also, given we are ignoring data blobs, the index entries in the list of index blobs don't need to include references to data blob ids (if an index entry exists, the corresponding data blob will surely exist). Note that removing data blobs from the specification reduces the state space because now the following two states from the previous specificion of last section are the same state in the refined specification -
	one in which a snapshot process wrote 4 contents A, B, C, D arranged in data blobs as A in the first data blob and B, C, D in the second one
	another in which a snapshot process wrote 3 contents A, B, C, D arranged in data blobs as A, B in the first data blob and C, D in the second one

Below is the refined set of state variables and steps after this change.

```
index_blobs_list,
(*  <<
    	<<[content_id |-> 0, deleted |-> TRUE/FALSE, timestamp |-> 0],
    	  [content_id |-> 1, deleted |-> TRUE/FALSE, timestamp |-> 0]>>,

    	<<[content_id |-> 4, deleted |-> TRUE/FALSE, timestamp |-> 0]>>
    >>
*)

snapshot_processess_bag,
(* 
    {
     [status |-> "in_progress",
      content_ids_to_be_written_list |-> <<5, 6, 7, 8, 9>>
      local_index_entries_set |-> {[content_id |-> 4, deleted |-> FALSE, timestamp |-> 0, location |-> 2], ...}
      local_data_blob_record |-> [content_ids_list |-> << 5, 6, 7>>],
      local_index_blob_list |-> <<[content_id |-> 5, deleted |-> FALSE, timestamp |-> 0, location |-> 3], ..>>
      start_timestamp |-> start_timestamp]: 2,
      ...
    }
*)

gcs_processes_bag,
(* {
        [local_snapshot_entries_bag |-> a bag of snapshot processes as above
         local_index_blobs_list |-> ...
         local_index_blob_list |-> ...
        ]: 2,
        ...
    }
*)

index_blob_compaction_processes_bag,
(* {
        [local_index_blobs_list |-> ...
         local_index_blob_list |-> ...
        ]: 2,
        ...
    }
*)
  
logical_timestamp

Steps -

1. Tick Time forward
2. Trigger a new snapshot process
3. Write contents as part of a snapshot process to local data blob and local index blob
4. Flush local data blob
4. Flush local index blob
5. Mark snapshot process complete
6. Delete snapshot
6. Trigger a new GC process
7. Add some content entries with deleted flag as True at the same timestamp to the local index blob
8. Flush local index blob
9. Trigger index blob compaction process
10. Write new merged index blob
11. Delete a subset of the old index blobs at the same timestamp from the set of index blobs to be deleted (those which have been compacted)
```

#### Avoiding semantically same, distinct states

I will usually call two states in TLA+ to be semantically equivalent and that means - the states might differ in some variable(s) and no temporal properties to be checked or sequence of steps that follow depend on this difference in values of the variable(s).

As per our current set of state variables in the specification, we can have the following two distinct states with MaxSnapshotTime as 2 for some values of the other constants with all other state variables having the same values -

```
	logical_timetamp = 3
	snapshot_processes_bag = {[status |-> "in_progress", \* Equivalent to a failed snapshot as logical_timestamp > start_timestamp + MaxSnapshotTime
							   contents_to_be_written_list |-> <<1, 2, 3, 4>>,
							   local_index_entries_set |-> {[content_id |-> 1, deleted |-> False, timestamp |-> 0], [content_id |-> 2, deleted |-> False, timestamp |-> 0]},
								index_blobs_to_be_flushed |-> <<>>,
								start_timestamp |-> 0]: 1}

	vs

	logical_timestamp = 3
	snapshot_processes = {[status |-> "in_progress", \* Equivalent to a failed snapshot as logical_timestamp > start_timestamp + MaxSnapshotTime
							contents_to_be_written_list |-> <<1, 2, 3>>,
							local_index_entries_set |-> {[content_id |-> 1, deleted |-> False, timestamp |-> 0], [content_id |-> 2, deleted |-> False, timestamp |-> 0]},
							index_blobs_to_be_flushed |-> <<>>,
							start_timestamp |-> 0]: 1}
```

Both states differ only in their set of contents_to_be_written_list and there are a lot of behaviours (let's denote the set by X) in which the step of writing further contents in these snapshots will not be taken. Also, no other steps other than writing further contents in these snapshots depends on contents_to_be_written_list. So the two states are semantically the same for the behaviours in X. The behaviours where further contents are written allow more contents to be written in both states (3, 4 can be written in the first and just 3 can be written in the second) but it can be seen that every behaviour possible in the second state will be covered in the first state as well with the difference in the field contents_to_be_written_list which is not used in any invariant.

Since the field contents_to_be_written_list just serves the purpose of deciding contents to be written for a snapshot on triggering (and the order in which they would be written) and then writing those contents in batches of blobs, we can get rid of this field and allow any snapshot process to write any content from the set of possible contents while being allowed to complete at any point in time. Making the snapshot process completion step as always enabled allows us to still capture all behaviours where different snapshots intend to write different sets of contents (in different orders) before completion.

We still have to maintain what contents the snapshot wrote along the way and so maintain a field contents_written_list instead. Contents are added to this list as they are written so that if the snapshot completes, we will know which contents it is composed of.

Below is the refined set of state variables and steps after this change.

```
index_blobs_list,
(*  <<
    	<<[content_id |-> 0, deleted |-> TRUE/FALSE, timestamp |-> 0],
    	  [content_id |-> 1, deleted |-> TRUE/FALSE, timestamp |-> 0]>>,

    	<<[content_id |-> 4, deleted |-> TRUE/FALSE, timestamp |-> 0]>>
    >>
*)

snapshot_processess_bag,
(* 
    {
     [status |-> "in_progress",
      contents_written_list |-> <<5, 6, 7, 8, 9>>
      local_index_entries_set |-> {[content_id |-> 4, deleted |-> FALSE, timestamp |-> 0, location |-> 2], ...}
      local_index_blob_list |-> <<[content_id |-> 5, deleted |-> FALSE, timestamp |-> 0, location |-> 3], ..>>
      start_timestamp |-> start_timestamp]: 2,
      ...
    }
*)

gcs_processes_bag,
(* {
        [local_snapshot_entries_bag |-> a bag of snapshot processes as above
         local_index_blobs_list |-> ...
         local_index_blob_list |-> ...
        ]: 2,
        ...
    }
*)

index_blob_compaction_processes_bag,
(* {
        [local_index_blobs_list |-> ...
         local_index_blob_list |-> ...
        ]: 2,
        ...
    }
*)
  
logical_timestamp

Steps -

1. Tick Time forward
2. Trigger a new snapshot process
3. Write **any contents from the possible contents** as part of a snapshot process to local data blob and local index blob
4. Flush local data blob
4. Flush local index blob
5. Mark snapshot process complete **(this step will now be enabled always)**
6. Delete snapshot
6. Trigger a new GC process
7. Add some content entries with deleted flag as True at the same timestamp to the local index blob
8. Flush local index blob
9. Trigger index blob compaction process
10. Write new merged index blob
11. Delete a subset of the old index blobs at the same timestamp from the set of index blobs to be deleted (those which have been compacted)
```

#### Behaviour pruning using Modus Tollens

Assume a disjoint set of behaviours X and Y allowed by the system. If we are able to establish a fact such as - if the safety condition breaks in Y => it will break in X, we can avoid captures the behaviours in Y in the specification. This is because if the safety condition doesn't break in X, we can be sure that it doesn't break in Y as well. This is just an application of Modus Tollens.

We know that safety will be violated only in behaviours with garbage collection where a content is marked deleted which is still referenced by a snapshot. The index compaction process after GC only sets it in stone that a content is lost forever.

**Refined safety condition** - For every content id present in a snapshot in the repository, an index entry with location of content data can be found after which there is no later entry for the index entry with the deleted flag as True.

So, our safety condition can be set up as this invariant - the latest index entry for a content id used by a snapshot shouldn't be marked deleted.

Let us now consider the follwoing:
	Y = the set of behaviours which include garbage collection and index compaction steps
	X = the set of behaviours which include garbage collection but no index compaction steps.

It is clear that if the invariant breaks in Y, it will break in X as well, since index compaction doesn't nothing more than remove the content's index entries forever. So we can prune our the behaviour space to be checked to exclude the behaviours in Y.

Below is the new set of state variables and steps after this change.

```
index_blobs_list,
(*  <<
    	<<[content_id |-> 0, deleted |-> TRUE/FALSE, timestamp |-> 0],
    	  [content_id |-> 1, deleted |-> TRUE/FALSE, timestamp |-> 0]>>,

    	<<[content_id |-> 4, deleted |-> TRUE/FALSE, timestamp |-> 0]>>
    >>
*)

snapshot_processess_bag,
(* 
    {
     [status |-> "in_progress",
      contents_written_list |-> <<5, 6, 7, 8, 9>>
      local_index_entries_set |-> {[content_id |-> 4, deleted |-> FALSE, timestamp |-> 0, location |-> 2], ...}
      local_index_blob_list |-> <<[content_id |-> 5, deleted |-> FALSE, timestamp |-> 0, location |-> 3], ..>>
      start_timestamp |-> start_timestamp]: 2,
      ...
    }
*)

gcs_processes_bag,
(* {
        [local_snapshot_entries_bag |-> a bag of snapshot processes as above
         local_index_blobs_list |-> ...
         local_index_blob_list |-> ...
        ]: 2,
        ...
    }
*)
  
logical_timestamp

Steps -

1. Tick Time forward
2. Trigger a new snapshot process
3. Write **any contents from the possible contents** as part of a snapshot process to local data blob and local index blob
4. Flush local data blob
4. Flush local index blob
5. Mark snapshot process complete **(this step will now be enabled always)**
6. Delete snapshot
6. Trigger a new GC process
7. Add some content entries with deleted flag as True at the same timestamp to the local index blob
8. Flush local index blob
```

#### Choose data structures of state variables wisely (just a special case of avoiding semantically distinct states)

\* How the contents are split into blobs while writing and the order in which they are written doesn't matter to checking safety of the system because no process in the implementation relies on splitting/ordering information of contents in blobs.

* Note that there is another case now with two semantically equivalent states -
	each with a snapshot that exceeded its timelimit to completion but the states differ in the contents_written_list (say there is an extra element in the one of them, call it S1) and
	the other state variables are the same (this can happen even if the snapshot in S1 wrote more one extra content than the snapshot in S2 because it might happen that in S2, that content was written by some other method)
	. Since, the snapshots can't be marked completed now, the two states are semantically equivalent. No step is now going to rely on this field's value (snapshots don't have to remember what they wrote because in case they choose a content they wrote they will anyway find it in the local set of index entries and not rewrite the content). This second optimization hasn't been done yet.

**Convert local\_index\_blobs\_list to local\_index\_entries\_set -** When a snapshot process starts up, it populates index entries from the list of index blobs into a single data structure and hence no step in any process relies on split/ordering information of index entries in index blobs. It doesn't matter if the index entries {A, B, C, D} were split while writing in index blobs as \<\<A, B>> and \<\<C, D>> or as blobs \<\<A>> and \<\<B, C, D>> or in any other manner. Moreover, for any split inturn, the ordering of index entries in the index blob doesn't matter. Hence, the states with different spilt/ordering of index entries in index blobs are semantically the same. And luckily we have already incorporated this fact by keeping a local_index_entries_set in a snapshot process record as compared to a the list local_index_blobs_list for a GC process. We don't need ordering information in the GC process either, so we can convert local_index_blobs_list to local_index_entries_set. Note that we convert it to a set and nto a bag because duplicate index entries don't affect what new indxe deletion entries would be written by the GC (the same is the reason for choosing a set instead of a bag for snapshot processes).

**Convert index\_blobs\_list to index\_entries\_set -** Since the split/ordering information of index entries in index blobs and the ordering information of index entries within blobs is never used now in any step (index compaction is gone! it would required the split information to delete index entries in blob units), we don't have to maintain a global list of index blobs either. We also don't have to maintain a bag instead of a set as no step relies to more than 1 index entry in the global set of index entries.

**Convert local\_index\_blob\_list to local\_index\_entries\_to\_flush\_set -** Note that since we are maintaining just a global set of index entries now, we can convert local\_index\_blob\_list in snapshot and GC process records to a set. We still have to maintain these fields even though splitting information is not maintained in the global set of index entries because the index entries are flushed to the global index in batches and we still have to mimic that behaviour. We can't mimic that by writing a subset of unwritten contents to the index because the index entries might have different timestamps and they get assigned only the logical timestamp which is incremented via a designated step in the specification (as an aside I tried to write the specification without having a logical timestamp field and writing a batch of index entries into the global index while mimicing the behaviour that the contents might be written at different timestamps by assigning increasing timestamp values to index entries; but the specification became hard to interpret).

To conclude, use unordered data structures such as bags and sets where ever possible in case the ordering information is not used in any step. This helps reduce the state space.

Below is the new set of state variables and steps after this change.

```
index_entries_set,
(*  {[content_id |-> 0, deleted |-> TRUE/FALSE, timestamp |-> 0],
     [content_id |-> 1, deleted |-> TRUE/FALSE, timestamp |-> 0]}
*)

snapshot_processess_bag,
(* 
    {
     [status |-> "in_progress",
      contents_written_list |-> <<5, 6, 7, 8, 9>>
      local_index_entries_set |-> ...
      local_index_entries_to_flush_set |-> ...
      start_timestamp |-> start_timestamp]: 2,
      ...
    }
*)

gcs_processes_bag,
(* {
        [local_snapshot_entries_bag |-> a bag of snapshot processes as above
         local_index_entries_set |-> ...
         local_index_entries_to_flush_set |-> ...
        ]: 2,
        ...
    }
*)
  
logical_timestamp

Steps -

1. Tick Time forward
2. Trigger a new snapshot process
3. Write **any contents from the possible contents** as part of a snapshot process to local data blob and local index blob
4. Flush local data blob
4. Flush local index blob
5. Mark snapshot process complete **(this step will now be enabled always)**
6. Delete snapshot
6. Trigger a new GC process
7. Add some content entries with deleted flag as True at the same timestamp to the local index blob
8. Flush local index blob
```

# Abstraction for GC2

The GC2 protocol is similar to GC but minor differences. There is a GC Mark process and another GC Repair/Discard process. The mark process is similar to vanilla GC - it adds idnex entries to mark certain content IDs deleted. The issue with GC was that an index entry with the deleted true marker would give the index compation process to delete all entries before and including that entry. It could be that another snapshot process running simultaneously with GC would have reused the content. So, what we need is the deletion entry to be just another stage in the content removal process and not the final verdict. For this there is a slight change in index compaction - not all content entries before the deleted marked entry are removed, but the entry with the deleted marker is retained. This is so that once a content is marked deleted, it is not removed forever before ensuring that no other snapshot had reused it while GC was marking it deleted (job of the Repair phase). We also need to ensure that if a content was not reused, then it is indeed deleted forever to free space (job of the discard phase). The Repair phase adds content entries without the deleted True marker in case it is reused by a snapshot which might have started before the GC mark phase that marked the content deleted. The GC discard phase runs just post the repair phase to remove index entries of content IDs including and before the deleted index entry in case it wasn't repaired in the repair phase and the entry was older than MaxSnapshotTime when checked for repairing.

Note that the discard phase is similar to the index compaction (just more privileged to even remove index entries with deleted marker) as it removes index entries and rewrites index blobs. But in our abstraction we ignored the split of index entries into blobs. The discard phase deletes blobs as a whole and since we are not keeping track of the information about how index entries were batched into blobs during snapshot processes, we might have to revert our specification to have index blobs instead of a just a single big set. We still don't need ordering information of index entries in blobs or the ordering of blobs itself. Take a pause and think about it. Now consider what if we don't keep track of splitting information in our behaviour and let the disard phase allow removal of index entries in any size batches (i.e., from the global set of index entries the discard process would know what index entries are to be deleted, and then it can delete those entries in batches)? Would consequences would this have? This kind of specification would surely capture that one behaviour in which the batch deletions by the discard step have the same splitting of index entires as how the index entries were flushed by different snapshot. However, it would allow many other behaviours which can never exist in the actual system. For example, the case where the discard phase is to delete index entries in batches which don't correspond to any split of how the index entries were actually flushed. But there is no harm in guaranteeing that safety doesn't break for these behaviours as well. But this will lead to a large state space. I didn't fix this in the specify just out of laziness since it didn't remove any behaviours where safety might be violated which might be of interest to me.