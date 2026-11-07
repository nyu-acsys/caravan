module type Value = sig
  val identity : int -> int
end

module Make (F : functor (Cell : Value) -> Value) = struct
  let identity (x : int) = x
end
