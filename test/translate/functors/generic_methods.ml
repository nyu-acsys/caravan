module type View = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  val read : t -> int
  (*@ result = read x requires counter x state ensures counter x state && result = state *)
end

module Make (Cell : View) = struct
  type t = Cell.t

  let read (x : t) = Cell.read x
  (*@ result = read x requires Cell.counter x state ensures Cell.counter x state && result = state *)

  let read_twice (x : t) =
    let first = read x in
    let second = read x in
    assert (first = second);
    second
  (*@ result = read_twice x requires Cell.counter x state ensures Cell.counter x state && result = state *)

  let rec repeat (x : t) n = if n <= 0 then read_twice x else repeat x (n - 1)
  (*@ result = repeat x n requires Cell.counter x state && n >= 0 ensures Cell.counter x state && result = state *)
end

module Actual_alias = Actual.First
module Make_alias = Make
module First = Make (Actual.First)
module Repeated = Make (Actual.First)
module Via_argument = Make (Actual_alias)
module Via_functor = Make_alias (Actual.First)
module Result_alias = First
module Other = Make (Actual.Second)

let first (x : First.t) =
  let value = First.repeat x 2 in
  assert (Repeated.read_twice x = value);
  assert (Via_argument.read x = value);
  assert (Via_functor.repeat x 1 = value);
  assert (Result_alias.read x = value);
  value
(*@ result = first x requires Actual.First.counter x state ensures Actual.First.counter x state && result = state *)

let other (x : Other.t) = Other.repeat x 3
(*@ result = other x requires Actual.Second.counter x state ensures Actual.Second.counter x state && result = state *)
