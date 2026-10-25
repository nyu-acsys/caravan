module type Argument = sig
  type t
end

module Actual = struct
  type t = int
end

module First_view : Argument = Actual
module Second_view : Argument = Actual
module View_alias = First_view

module Make (X : Argument) = struct
  type value = Value of int
  type cell = { mutable contents : int }

  let identity (x : value) = x
  (*@ result = identity x ensures result = x *)
end

module First = Make (First_view)
module Repeated = Make (First_view)
module Aliased = Make (View_alias)
module Second = Make (Second_view)

let check () =
  let a = { First.contents = 0 } in
  let b = { Second.contents = 1 } in
  a.Repeated.contents <- 7;
  assert (a.Aliased.contents = 7);
  assert (b.Second.contents = 1);
  match Aliased.identity (Repeated.identity (First.Value 7)) with
  | Repeated.Value x -> assert (x = 7)
