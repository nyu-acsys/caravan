# Bounded queue cache experiment

The Saturn bounded queue has two different ordinary integer fields on each node:

| Field | Before publication | After publication |
| --- | --- | --- |
| `counter` | Initialized, then assigned the predecessor's counter plus one | Frozen |
| `capacity` | Initialized, then assigned the predecessor's observed capacity minus one | May be refreshed from acquired head and tail counters |

A successful link publishes a new node. Readers reach nodes through the atomic
head, tail, or next links. The source bridge must propagate the corresponding
publication view, including through helping operations. Publication of a node
must exclude earlier private writes when interpreting later ordinary reads.

The mutable capacity cache cannot use the frozen-field rule. A reader can observe
a stale post-publication capacity. This is useful because positive cache entries
are conservative: for a fixed tail position, an advancing head only increases
the available capacity. If a positive cached capacity permits a push, decrementing
it supplies a conservative initial capacity for the new tail node. A zero cache
does not establish fullness: the implementation acquires the head, recomputes the
bound, and may refresh the old tail's capacity before retrying.

`cached_counter.rav` checks this arithmetic using a past-write journal. Its
abstract read operation explicitly distinguishes unrestricted history reads from
reads with an established publication cut. Only the abstract read uses
`havoc`/`assume`; the cache bound is proved from recorded events and head ordering.
`advance_cache_bound` states the general stability argument for any certified
entry, independent of which finite history the example records. The three
negative tests reject private initialization values without a cut,
the claim that acquisition selects the latest write, and a head position that
regresses after the cache refresh.

This is a protocol experiment, not a verification of the bounded queue. The
shared `ThreadContext` binds the cut to the executing identity and the history
released on the acquired channel. The abstract read consults that context rather
than accepting a user-chosen acquisition flag. Establishing that this cut excludes
earlier private source writes, proving all future cache writes preserve the bound
under interference, and accounting for machine-integer wraparound remain
separate obligations. The mathematical
positions used here do not establish a modular-arithmetic ordering for source
counters. The constructor's private-write history is retained deliberately, so
the missing-acquire test exercises an observable difference.
