module type Queue = sig
  (*@ predicate contents (cell : int Atomic.t) (xs : int sequence) *)

  val push : int Atomic.t -> unit
  (*@ push cell
      requires contents cell xs
      ensures contents cell (xs ++ [true]) *)
end

module Impl : Queue = struct
  let push cell = Atomic.set cell 0
end
