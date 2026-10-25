module type Value = sig
  val identity : int -> int
end

module Make (Left : Value) (Right : Value) = struct
  let identity x = Left.identity (Right.identity x)
end
