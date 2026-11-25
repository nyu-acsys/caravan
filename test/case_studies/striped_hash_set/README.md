# Striped hash set

An independent OCaml implementation of the lock-striped hash-set design in
Herlihy and Shavit's *The Art of Multiprocessor Programming*, Section 13.2.2.
A fixed array of mutexes protects rows of bucket lists. Each nonnegative integer
key selects a stripe and then a bucket within that stripe.

This case study covers `create`, `contains`, `add`, `remove`, and `resize`.
The table pointer and the heuristic element counter are atomic; bucket cells use
ordinary ownership under their stripe's mutex.

The companion proof tracks a finite abstract set partitioned between the
stripes. Each stripe lock holds half of a ghost snapshot, and the client contents
predicate holds the other half. Operations reconcile and update these snapshots
while holding the selected mutex, committing their logical step before unlock.
The counter is updated after unlock and is not specified as exact cardinality.

`resize set expected_capacity` acquires every stripe in index order. If the first
row still has the expected capacity and doubling fits the maximum array length,
it rehashes every row into a fresh table and publishes that table before
releasing the locks. A stale request does nothing. Each old row is scanned using
its own length; the proof needs no assumption that old rows have equal capacities.

The resize proof gathers the stripes' table-agreement fragments, updates the
complete agreement at publication, and redistributes the fragments before
unlocking. Each stripe retains its abstract set. The client's `contents` resource
is preserved by framing, so resizing needs no client atomic update. Its rehashing
and lock-set lemmas are checked with the implementation. The public contract
specifies set preservation and lock cleanup; it does not expose capacity growth.

Automatic load-factor-based resizing is not implemented.

An interface-only client checks collisions, duplicate insertion, missing-key
removal, independent stripes, and set preservation across sequences of resize
requests using the abstract contracts. It also covers empty sets and a
single stripe. Negative tests reject an incorrect duplicate-insertion result
and a nonpositive resize request.

The constructor currently requires between 1 and 1,000 stripes. Keys must be
nonnegative, and resize requests must have a positive expected capacity. Set
operations and resize require an empty incoming held-lock set. The proof checks
preservation of the caller's held-lock context; it does not establish termination,
fairness, or deadlock freedom.

Run the case-study regression with:

```bash
dune build @test/case_studies/striped_hash_set/runtest -j2
```
