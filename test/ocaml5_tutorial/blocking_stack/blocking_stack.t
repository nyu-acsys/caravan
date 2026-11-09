The unchanged tutorial stack verifies against a polymorphic LIFO model.

  $ caravan --shh blocking_stack.ml
  Verification successful.
  $ caravan --shh --emit-rav blocking_stack.ml > blocking_stack.rav
  $ raven --shh blocking_stack.rav
  Verification successful.

Discarding the previous contents does not implement push's abstract step.

  $ cp blocking_stack.mli bad_push.mli
  $ cp blocking_stack.proof bad_push.proof
  $ sed 's/r.contents <- v::r.contents/r.contents <- [v]/' blocking_stack.ml > bad_push.ml
  $ ! caravan --shh bad_push.ml > bad_push.out 2>&1
  $ grep -q 'Failed to fold predicate' bad_push.out

Leaving the popped element in place violates the loop's resource postcondition.

  $ sed 's/r.contents <- xs/r.contents <- x::xs/' blocking_stack.ml > bad_pop.ml
  $ cp blocking_stack.mli bad_pop.mli
  $ cp blocking_stack.proof bad_pop.proof
  $ ! caravan --shh bad_pop.ml > bad_pop.out 2>&1
  $ grep -q 'A postcondition may not hold' bad_pop.out

The client cannot prove FIFO order for a LIFO stack.

  $ cp blocking_stack.ml bad_order.ml
  $ cp blocking_stack.mli bad_order.mli
  $ sed 's/result === (42, 17)/result === (17, 42)/' blocking_stack.proof > bad_order.proof
  $ ! caravan --shh bad_order.ml > bad_order.out 2>&1
  $ grep -q 'A postcondition may not hold' bad_order.out
