module type Queue = sig
  (*@ predicate contents (cell : int Atomic.t) (xs [@implicit] : int sequence) *)

  val push : int Atomic.t -> int -> unit
  (*@ push cell value
      requires contents cell xs
      ensures contents cell (xs ++ [value]) *)

  val push_twice : int Atomic.t -> int -> int -> unit
  (*@ push_twice cell first second
      requires contents cell xs
      ensures contents cell (xs ++ ([first] ++ [second])) *)
end

module Impl : Queue = struct
  let push cell value = Atomic.set cell value
  let push_twice cell _first second = Atomic.set cell second
end
