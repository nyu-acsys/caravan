module type Value = sig
  val identity : int -> int
end

module Make (Cell : Value) = struct
  let identity x = Cell.identity x
end

module Client = Make (struct
  let identity (x : int) = x
end)
