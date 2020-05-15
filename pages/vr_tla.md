---
layout: page
title: TLA+ for ViewStamped Repilcation
images:
  - image: /assets/images/img1.jpg
  - image: /assets/images/img2.jpg
carousel:
  - image: /assets/images/img1.jpg
  - image: /assets/images/img2.jpg
---


ViewStamped Replication is a consensus protocol used to realise a replicated state machine [^1].

[^1]: Viewstamped Replication Revisited - [http://pmg.csail.mit.edu/papers/vr-revisited.pdf](http://pmg.csail.mit.edu/papers/vr-revisited.pdf)

This TLA+ spec verifies safety of the ViewStamped Replication protocol as describes in the paper (with the exception that the reconfiguration protocol is not verified yet. I plan to verify the safety of that as well in the coming weeks). The [specification](https://github.com/pkj415/ViewStamped-Replication-TLA/blob/master/ViewStampedReplication.tla) explains the state variables used and the steps. Verifying liveness is impossible as per [^2].

[^2]: The FLP Impossibility rule - [https://groups.csail.mit.edu/tds/papers/Lynch/jacm85.pdf](https://groups.csail.mit.edu/tds/papers/Lynch/jacm85.pdf)

The state variables include each process' state as describes in the paper and a set that represents the messages in the network. The steps in the specification are self explanatory as mentioned in the paper. The specification captures all behaviours possible in an asynchronous world. In the step where any process intends to send a message to another process, the message is added to the messages set. The step to receive a message simple reads the message from the set without removing it. Incorporating asynchrony relies on the fact that the elements added to the messages set are never removed. This allows receiving a message more than once (allow behaviours with duplicates of a message in the network); any step that is enabled by the presence of a particular element in the messages set among other preconditions, will still remain enabled if the other preconditions stay true i.e., if there exists a behaviour where a process receives and takes a step based on duplicate messages, the behaviour will be traversed by TLC. Also, there are no time bounds on receiving a message - once a step becomes enabled after a specific message is present in the messages set, the step can be taken at any point later till the step remains enabled (it can possible get disabled due to other preconditions). Also, a lost message is captured by the behaviour in which such an enabled step that corresponds to receiving the message in never taken.

In case of a broadcast message, the message added to the messages set need not contain the "to" field. Any message without a "to" field implicity means that any process can execute a step that captures receiving a broadcast message. This is an example of abstracting away from the lower level implementation in which case the broadcast might require a "to" field.

## Safety conditions -

To verify safety, we check if the specification implements the [LinearizableOrdering](https://github.com/pkj415/ViewStamped-Replication-TLA/blob/master/LinearizableOrdering.tla) specification. The LinearizableOrdering specification is a "what" specification while the spec for ViewStamped Replication is a "how" specification. The LinearizableOrdering specification just has a state variable ordering which represents a tuple (i.e., an ordered sequence) of client commands. The only step possible in this specification is to extend ordering by a sequence of client commands which are not already in the tuple. The ViewStamped Replication protocol intends to acheive this - any behaviour should appear to be a behaviour of the LinearizableOrdering spec i.e., client commands are executed in some order and the order can only be extended (client commands already part of the externally visible ordering can't be changed/ removed and new client commands can't appear anywhere in between an ordering). The "what" specification is named Linearizable because VR is intended to acheive Linearizable consistency. The ordering in the specification represents the visiblity/ arbitration/ returns before order as defined by Linearizability in [^3] and the ordering variable in the VR spec represents the arbitration order. And in VR, since each client request is executed based on the application state present after executing previous requests, the effect of the previous client requests is visible to any request being executed. And hence, the visibility order is the same as the arbitration order. is the same as the ordering. Also, the returns before ordering has to be a subset of the arbitration ordering for Linearizability and this is ensured in VR by the the fact that a response is issued for a client request only after it has committed and hence, any other request which comes later in the returns before ordering will surely be executed after the request earlier in the rb ordering.

[^3]: Principles of eventual consistency - [https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/final-printversion-10-5-14.pdf](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/final-printversion-10-5-14.pdf)

Apart from checking if the VR specification implements the LinearizableOrdering spec, I had added a few invariants specific to VR protocol to the specification. This was just to ensure the spec is not allowing behaviours that are unintended i.e., the spec is error free. As an aside - when making changes to the spec (such as adding new variantions or extending the protocol), I would usually check some temporal properties to ensure that the spec is also allowing the behaviours that are intended and not just blocking behaviours that are unintended. An example of such a temportal property would be - eventually all client commands are committed (note that this will happen because - i.) the specification doesn't allow infinite view changes, only a maximum number as specified in the constants and ii.) the specification doesn't allow trivial behaviours that don't make progress (also called stuttering steps) and this is done using weak fairness conditions which are enforced on all steps).

To ensure that all behaviours allowed by ViewStampedReplication spec satisfy LinearizableOrdering spec, the state in ViewStampedReplication spec contains the ordering variable which represents the ordering of commands executed by VR as seen by the outside world. In case a sequence of client commands are committed by the leader, they are appended to ordering.

## Capturing behaviours with failures and recovery -

To verify correctness of VR, we also have to capture failures and recoveries in the protocol and this is done by the FailNode step in the spec which is always enabled if more than a majority of the nodes are alive (i.e., not in "recovering" status).
