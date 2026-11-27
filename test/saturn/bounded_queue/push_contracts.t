Insertion clients use exact capacity conditions for successful and failed calls,
including zero capacity and reuse after removal.

  $ cat bounded_queue.ml helper_clients.ml > push_clients.ml
  $ cat bounded_queue.mlp helper_clients.mlp > push_clients.mlp
  $ caravan --shh -I ../backoff --only Push_contract_clients push_clients.ml
  Verification successful.

The serialized proof retains its prophecy types and contracts.

  $ caravan --shh -I ../backoff --emit-rav push_clients.ml > push_clients.rav
  $ raven --shh --typeonly push_clients.rav
  Verification successful.

A nonfull queue cannot reject insertion.

  $ cp push_clients.ml rejected.ml
  $ sed 's/accepted \&\& observed === Some value/not accepted \&\& observed === Some value/' push_clients.mlp > rejected.mlp
  $ caravan --shh -I ../backoff --only Push_contract_clients.push_available rejected.ml > rejected.out 2>&1
  [1]
  $ grep -q 'Verification Error:' rejected.out
  $ grep -qi timeout rejected.out
  [1]
