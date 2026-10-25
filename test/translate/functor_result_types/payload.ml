module type Value = sig
  type t

  val identity : t -> t
  (*@ result = identity x ensures result = x *)
end

module Integers = struct
  type t = int

  let identity (x : t) = x
  (*@ result = identity x ensures result = x *)
end

module Booleans = struct
  type t = bool

  let identity (x : t) = x
  (*@ result = identity x ensures result = x *)
end

module Make (Cell : Value) = struct
  type t = Wrap of Cell.t
  type box = { cell : t }
  type holder = { mutable value : t }

  let wrap x = Wrap (Cell.identity x)
  (*@ result = wrap x ensures result = Wrap x *)

  let unwrap value = match value with Wrap x -> Cell.identity x
  (*@ result = unwrap value ensures match value with Wrap x -> result = x *)

  let read (h : holder) = h.value
  (*@ result = read h requires own h.value value ensures own h.value value && result = value *)

  let box x = { cell = x }
  (*@ result = box x ensures result.cell = x *)
end

module Left = Make (Integers)
module Right = Make (Integers)
module Boolean = Make (Booleans)

let check () =
  let h = { Left.value = Left.wrap 7 } in
  let box = Right.box (Right.read h) in
  assert (Left.unwrap box.Right.cell = 7);
  assert (Boolean.unwrap (Boolean.wrap true))
