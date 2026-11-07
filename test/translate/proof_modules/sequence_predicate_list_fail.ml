module type Queue = sig
  (*@ predicate contents (cell : int Atomic.t) (xs : int sequence) *)

  val push : int Atomic.t -> int list -> unit
  (*@ push cell values
      requires contents cell xs
      ensures contents cell (xs ++ values) *)
end

module Impl : Queue = struct
  let push cell _values = Atomic.set cell 0
end
