The extracted implementation, with validated fullness queries and insertion,
verifies with its queue protocol. This run starts with a fresh verification cache shared by its commands.

  $ mkdir verification-cache
  $ caravan --shh -I ../backoff --cache-dir verification-cache bounded_queue.ml
  Verification successful.

One combined client program exercises cleared dummy words, reordered labelled
arguments, integer and Boolean payloads, default and explicit capacities, private
initialization, stale eligible caches, link publication, failed retries, tail helping,
both public push wrappers, peeks, removals, capacity reuse after clearing, and
exact emptiness, fullness, and length observations.

  $ cat bounded_queue.ml > clients.ml
  $ cat >> clients.ml <<'ML'
  > let dummy () : (bool, [ `Node ]) node =
  >   make_node ~value:(Obj.magic ()) ~capacity:3 ~counter:0 Null
  > 
  > let integer () = make_node ~counter:1 ~value:42 ~capacity:2 Null
  > let boolean () = make_node ~capacity:1 ~value:true ~counter:2 Null
  > let default () : int t = create ()
  > let explicit () : bool t = create ~capacity:3 ()
  > let forwarded () : int t = create ?capacity:(Some 0) ()
  > ML
  $ cat helper_clients.ml >> clients.ml
  $ cat bounded_queue.mlp > clients.mlp
  $ cat >> clients.mlp <<'PROOF'
  > proof result = dummy ()
  >   ensures (allocated Ghost.self result (None : bool option) 3 0 Null) = ()
  > 
  > proof result = integer ()
  >   ensures (allocated Ghost.self result (Some 42) 2 1 Null) = ()
  > 
  > proof result = boolean ()
  >   ensures (allocated Ghost.self result (Some true) 1 2 Null) = ()
  > proof result = default () ensures (empty_queue Ghost.self result max_int) = ()
  > proof result = explicit () ensures (empty_queue Ghost.self result 3) = ()
  > proof result = forwarded () ensures (empty_queue Ghost.self result 0) = ()
  > PROOF
  $ cat helper_clients.mlp >> clients.mlp
  $ caravan --shh -I ../backoff --cache-dir verification-cache clients.ml
  Verification successful.

The same combined client program verifies after serialization to native Raven.

  $ caravan --shh -I ../backoff --emit-rav clients.ml > clients.rav
  $ raven --shh --smt-timeout=30000 --cache-dir verification-cache clients.rav
  Verification successful.

The constructor does not turn a cleared word into an initialized payload.

  $ sed 's/(None : bool option)/(Some true : bool option)/' clients.mlp > wrong.mlp
  $ cp clients.ml wrong.ml
  $ caravan --shh -I ../backoff --cache-dir verification-cache --only dummy wrong.ml > wrong.out 2>&1
  [1]
  $ grep -q 'Verification Error:' wrong.out
  $ grep -qi timeout wrong.out
  [1]

Freezing a failed candidate prevents the counter rewrite required by a retry.

  $ sed '/let prior = Counter.release_private candidate in/a\
  > \    Counter.freeze candidate;' clients.mlp > frozen_candidate.mlp
  $ cp clients.ml frozen_candidate.ml
  $ caravan --shh -I ../backoff --cache-dir verification-cache --only failed_retry frozen_candidate.ml > frozen.out 2>&1
  [1]
  $ grep -q 'Verification Error:' frozen.out
  $ grep -qi timeout frozen.out
  [1]

A relaxed cache read cannot promise the most recent value.

  $ sed 's/Set.mem (event, result) eligible)/Set.mem (event, result) eligible \&\& result = current)/' bounded_queue.mlp > latest.mlp
  $ cp bounded_queue.ml latest.ml
  $ caravan --shh -I ../backoff --cache-dir verification-cache --only get_capacity latest.ml > latest.out 2>&1
  [1]
  $ grep -q 'Verification Error:' latest.out
  $ grep -qi timeout latest.out
  [1]

An arbitrary set of event identifiers is not visibility evidence.

  $ sed -e "s/proof result = link_candidate value/proof result = link_candidate [forged : Ghost.t set] value/" -e '/proof result = link_candidate /,/proof result = failed_retry /s/Ghost.merge_views Ghost.self counter_view fields_view/Ghost.merge_views Ghost.self counter_view forged/' clients.mlp > forged.mlp
  $ cp clients.ml forged.ml
  $ caravan --shh -I ../backoff --cache-dir verification-cache --only link_candidate forged.ml > forged.out 2>&1
  [1]
  $ grep -q 'Verification Error:' forged.out
  $ grep -qi timeout forged.out
  [1]

Null links are rejected by the checked conversion helper.

  $ cat bounded_queue.ml > null_link.ml
  $ cp bounded_queue.mlp null_link.mlp
  $ cat >> null_link.ml <<'ML'
  > let bad_null () : (int, [ `Node ]) node = link_as_node (Link Null)
  > ML
  $ caravan --shh -I ../backoff --cache-dir verification-cache --only bad_null null_link.ml > null.out 2>&1
  [1]
  $ grep -q 'Verification Error:' null.out
  $ grep -qi timeout null.out
  [1]

An empty queue cannot yield a payload through peek_opt.

  $ sed 's/proof result = peek_empty () ensures (result === None)/proof result = peek_empty () ensures (result === Some true)/' clients.mlp > wrong_peek.mlp
  $ cp clients.ml wrong_peek.ml
  $ caravan --shh -I ../backoff --cache-dir verification-cache --only peek_empty wrong_peek.ml > peek.out 2>&1
  [1]
  $ grep -q 'Verification Error:' peek.out
  $ grep -qi timeout peek.out
  [1]

An empty queue cannot yield a payload through pop_opt.

  $ sed 's/proof result = pop_empty () ensures (result === None)/proof result = pop_empty () ensures (result === Some true)/' clients.mlp > wrong_pop.mlp
  $ cp clients.ml wrong_pop.ml
  $ caravan --shh -I ../backoff --cache-dir verification-cache --only pop_empty wrong_pop.ml > pop.out 2>&1
  [1]
  $ grep -q 'Verification Error:' pop.out
  $ grep -qi timeout pop.out
  [1]

A freshly created queue must be reported empty.

  $ sed 's/proof result = empty_query () ensures (result)/proof result = empty_query () ensures (not result)/' clients.mlp > wrong_empty.mlp
  $ cp clients.ml wrong_empty.ml
  $ caravan --shh -I ../backoff --cache-dir verification-cache --only empty_query wrong_empty.ml > empty.out 2>&1
  [1]
  $ grep -q 'Verification Error:' empty.out
  $ grep -qi timeout empty.out
  [1]

Fullness is exact, including the transition back to nonfull after removal.

  $ sed 's/not before \&\& during \&\& count = 1 \&\& not after/not before \&\& not during \&\& count = 1 \&\& not after/' clients.mlp > wrong_full.mlp
  $ cp clients.ml wrong_full.ml
  $ caravan --shh -I ../backoff --cache-dir verification-cache --only fullness_cycle wrong_full.ml > full.out 2>&1
  [1]
  $ grep -q 'Verification Error:' full.out
  $ grep -qi timeout full.out
  [1]
