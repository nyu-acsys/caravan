The complete segment queue proof is shared by two fresh functor applications.
Clients exercise list initialization, FIFO operations, aliases, and independent queues.

  $ caravan --shh -I ../../saturn/backoff --smt-timeout=30000 segment_queue.ml
  Verification successful.
  $ caravan --shh -I ../../saturn/backoff --emit-rav segment_queue.ml > emitted.rav
  $ raven --shh --smt-timeout=30000 emitted.rav
  Verification successful.

The emitted program has one worker and one copy of the queue body and local builder.
Each application receives a fresh layout.

  $ grep -c 'Generic_.*\[Parameter:' emitted.rav
  1
  $ grep -c '^[[:space:]]*proc method_push(' emitted.rav
  1
  $ grep -c '^[[:space:]]*proc method_build_next(' emitted.rav
  1
  $ grep -c '^module Layout.* = .*\.Fresh()' emitted.rav
  2

The result signature hides implementation helpers.

  $ cat segment_queue.ml > hidden.ml
  $ echo 'let hidden = First.fix_tail' >> hidden.ml
  $ ! caravan --shh -I ../../saturn/backoff hidden.ml > hidden.out 2>&1
  $ grep -q 'Unbound value First.fix_tail' hidden.out

A queue from one fresh application cannot be passed to the other.

  $ cat segment_queue.ml > crossed.ml
  $ echo 'let crossed (q : First.t) = Second.pop_opt q' >> crossed.ml
  $ ! caravan --shh -I ../../saturn/backoff crossed.ml > crossed.out 2>&1
  $ grep -q 'Type Error:' crossed.out
  $ ! grep -q 'Internal Error:' crossed.out

Interface clients reject an incorrect FIFO result.

  $ echo 'module Alias = Segment_api.Queue' > wrong_client.ml
  $ sed 's/assert (Alias.pop_opt q = Some 1)/assert (Alias.pop_opt q = Some 9)/' segment_client.ml >> wrong_client.ml
  $ ! caravan --shh wrong_client.ml > wrong_client.out 2>&1
  $ grep -q 'Verification Error: This assertion may be violated.' wrong_client.out
  $ ! grep -Eq 'Internal Error:|Syntax Error:' wrong_client.out
