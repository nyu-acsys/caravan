The complete history queue proof verifies behind a static module signature, with
clients using the same resources through an alias.

  $ caravan --shh -I ../../saturn/backoff --smt-timeout=30000 module_queue.ml
  Verification successful.

The complete emitted module proof verifies as standalone Raven.

  $ caravan --shh -I ../../saturn/backoff --emit-rav module_queue.ml > emitted.rav
  $ raven --shh --smt-timeout=30000 emitted.rav
  Verification successful.

The alias client must respect FIFO order.

  $ echo 'module Alias = Queue_api.Queue' > wrong_client.ml
  $ sed 's/assert (Alias.pop_opt q = Some 1)/assert (Alias.pop_opt q = Some 9)/' client.ml >> wrong_client.ml
  $ caravan --shh wrong_client.ml 2>&1 | grep -F 'Verification Error:'
  Verification Error: This assertion may be violated.
