Wrapped counters represent unbounded logical positions. Positive refreshes and
successor cache entries remain conservative as the head and tail advance;
retained old nodes may lie behind the head and have capacity above the limit.
The combined source example crosses max_int while retaining an old node.

  $ caravan --shh moving_capacity.ml
  Verification successful.
  $ caravan --shh --emit-rav moving_capacity.ml > moving_capacity.rav
  $ raven --shh moving_capacity.rav
  Verification successful.

A successful successor must decrement its predecessor's capacity certificate.

  $ sed 's/Some { capacity = capacity - 1 }/Some { capacity = capacity }/' moving_capacity.ml > no_decrement.ml
  $ cp moving_capacity.proof no_decrement.proof
  $ caravan --shh no_decrement.ml > no_decrement.out 2>&1
  [1]
  $ grep -q 'Verification Error:' no_decrement.out
  $ grep -qi 'timeout' no_decrement.out
  [1]

Adding one to a refresh can overestimate the logical availability.

  $ sed 's/let available = limit - length in/let available = limit - length + 1 in/' moving_capacity.ml > overestimate.ml
  $ cp moving_capacity.proof overestimate.proof
  $ caravan --shh overestimate.ml > overestimate.out 2>&1
  [1]
  $ grep -q 'Verification Error:' overestimate.out
  $ grep -qi 'timeout' overestimate.out
  [1]

Source counters need not increase when their logical position increases.

  $ cp moving_capacity.ml monotone.ml
  $ sed '/proof result = successor /a\
  > \  ensures (result > counter)' moving_capacity.proof > monotone.proof
  $ caravan --shh monotone.ml > monotone.out 2>&1
  [1]
  $ grep -q 'Verification Error:' monotone.out
  $ grep -qi 'timeout' monotone.out
  [1]

Nonpositive refreshes do not prove fullness for arbitrarily delayed tail
observations. With limit=max_int and a head one position beyond the retained
tail, mathematical availability is max_int+1 but the source computes min_int.
The baseline proves that its fullness test returns true; claiming otherwise fails.

  $ cp moving_capacity.ml false_full.ml
  $ sed 's/proof result = stale_tail_full () ensures (result === true)/proof result = stale_tail_full () ensures (result === false)/' moving_capacity.proof > false_full.proof
  $ caravan --shh false_full.ml > false_full.out 2>&1
  [1]
  $ grep -q 'A postcondition may not hold' false_full.out
  $ grep -qi 'timeout' false_full.out
  [1]
