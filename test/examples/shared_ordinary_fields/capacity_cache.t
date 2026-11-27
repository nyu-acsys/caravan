The source cache keeps explicit relaxed write journals. Certified capacities
remain conservative as the atomic head advances. A refresh uses a persistent
snapshot of an earlier head, so interference before the write is permitted.
Executable arithmetic stays within the machine-int bounds of this fixed-tail
epoch. All proof annotations are in the companion file.

  $ caravan --shh capacity_cache.ml
  Verification successful.
  $ caravan --shh --emit-rav capacity_cache.ml > capacity_cache.rav
  $ raven --shh capacity_cache.rav
  Verification successful.

A refresh cannot overestimate capacity, and the head cannot regress.

  $ sed 's/limit - (tail - observed_head)/limit - (tail - observed_head) + 1/' capacity_cache.ml > over_refresh.ml
  $ cp capacity_cache.mlp over_refresh.mlp
  $ caravan --shh over_refresh.ml > over_refresh.out 2>&1
  [1]
  $ grep -q 'Verification Error:' over_refresh.out
  $ grep -qi 'timeout' over_refresh.out
  [1]
  $ sed 's/previous + 1/previous - 1/g' capacity_cache.ml > regression.ml
  $ sed 's/previous + 1/previous - 1/g' capacity_cache.mlp > regression.mlp
  $ caravan --shh regression.ml > regression.out 2>&1
  [1]
  $ grep -q 'Verification Error:' regression.out
  $ grep -qi 'timeout' regression.out
  [1]

A stale positive cache value is safe, but need not equal the latest write.

  $ cp capacity_cache.ml latest.ml
  $ sed 's/ensures (result === 0 || result === 2)/ensures (result === 2)/' capacity_cache.mlp > latest.mlp
  $ caravan --shh latest.ml > latest.out 2>&1
  [1]
  $ grep -q 'A postcondition may not hold' latest.out
  $ grep -qi 'timeout' latest.out
  [1]

Assignment anchors match both the field and the assigned expression.

  $ cp capacity_cache.ml wrong_anchor.ml
  $ sed 's/at (cache.capacity <- available)/at (cache.capacity <- 0)/' capacity_cache.mlp > wrong_anchor.mlp
  $ caravan --shh wrong_anchor.ml > wrong_anchor.out 2>&1
  [1]
  $ grep -q 'This anchor matches no code of refresh' wrong_anchor.out

The publication variant retains an unsafe private initialization in its full
journal. Only the eligible journal carries the capacity certificate, so its
read proof needs the acquired published-read rule.

  $ cp capacity_cache.ml unfiltered.ml
  $ sed 's/at (cache.capacity) Ghost.published_scope/at (cache.capacity) Ghost.scope/' capacity_cache.mlp > unfiltered.mlp
  $ caravan --shh unfiltered.ml > unfiltered.out 2>&1
  [1]
  $ grep -q 'Verification Error:' unfiltered.out
  $ grep -qi 'timeout' unfiltered.out
  [1]
