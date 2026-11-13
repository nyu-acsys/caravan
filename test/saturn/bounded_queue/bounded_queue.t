Saturn's constructors own their link cells, payload/capacity journals, and counters.

  $ caravan --shh bounded_queue.ml
  Verification successful.

Concrete clients exercise dummy words and reordered labelled arguments without
changing the extracted upstream implementation.

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
  $ cat bounded_queue.proof > clients.proof
  $ cat >> clients.proof <<'PROOF'
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
  $ caravan --shh clients.ml
  Verification successful.
  $ caravan --shh --emit-rav clients.ml > clients.rav
  $ raven --shh clients.rav
  Verification successful.

The constructor does not turn a cleared word into an initialized payload.

  $ sed 's/(None : bool option)/(Some true : bool option)/' clients.proof > wrong.proof
  $ cp clients.ml wrong.ml
  $ caravan --shh wrong.ml > wrong.out 2>&1
  [1]
  $ grep -q 'Verification Error:' wrong.out
  $ grep -qi timeout wrong.out
  [1]
