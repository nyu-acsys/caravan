Verify a one-step queue-tail advancement against both invariant representations.
The operation requires the queue invariant and preserves the FIFO view by framing.

  $ caravan --shh -I ../../saturn/backoff --smt-timeout=30000 michael_scott_queue.ml
  Verification successful.

  $ caravan --shh -I ../../saturn/backoff --smt-timeout=30000 michael_scott_queue_lseg.ml
  Verification successful.
