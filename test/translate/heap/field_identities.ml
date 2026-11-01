type intList = Box of int

let named () =
  let cell = Atomic.make (Box 1) in
  let old = Atomic.exchange cell (Box 2) in
  let current = Atomic.get cell in
  (old, current)
(*@ result = named () ensures result === (Box 1, Box 2) *)

let listed () =
  let cell = Atomic.make [ 1 ] in
  let old = Atomic.exchange cell [ 2 ] in
  let current = Atomic.get cell in
  (old, current)
(*@ result = listed () ensures result === ([1], [2]) *)

let refs () =
  let named = ref (Box 1) in
  let listed = ref [ 1 ] in
  named := Box 2;
  listed := [ 2 ];
  (!named, !listed)
(*@ result = refs () ensures result === (Box 2, [2]) *)

let tuple_left () =
  let cell = Atomic.make (1, (true, ()), 2) in
  let old = Atomic.exchange cell (3, (false, ()), 4) in
  (old, Atomic.get cell)
(*@ result = tuple_left ()
    ensures result === ((1, (true, ()), 2), (3, (false, ()), 4)) *)

let tuple_right () =
  let cell = Atomic.make ((1, true, ()), 2) in
  let old = Atomic.exchange cell ((3, false, ()), 4) in
  (old, Atomic.get cell)
(*@ result = tuple_right ()
    ensures result === (((1, true, ()), 2), ((3, false, ()), 4)) *)

type a_b = { mutable c : int }
type a = { mutable b_c : bool }

let records () =
  let first = { c = 1 } in
  let second = { b_c = false } in
  first.c <- 2;
  second.b_c <- true;
  (first.c, second.b_c)
(*@ result = records () ensures result === (2, true) *)

let pointer_payloads () =
  let first = ref 1 in
  let second = ref 2 in
  let no = ref false in
  let yes = ref true in
  let integers = Atomic.make first in
  let booleans = Atomic.make no in
  assert (Atomic.compare_and_set integers first second);
  let old = Atomic.exchange booleans yes in
  assert (old == no);
  assert (Atomic.get integers == second);
  assert (Atomic.get booleans == yes);
  !second
(*@ result = pointer_payloads () ensures result = 2 *)
