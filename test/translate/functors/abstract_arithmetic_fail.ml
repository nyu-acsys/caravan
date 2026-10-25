module type View = sig
  type t

  val identity : t -> t
  (*@ result = identity x ensures result = x *)
end

module Implementation = struct
  type t = int

  let identity (x : int) = x
  (*@ result = identity x ensures result = x *)
end

module Make (Cell : View) = struct
  let identity (x : Cell.t) = Cell.identity x
  (*@ result = identity x ensures result = x + 1 *)
end

module Client = Make (Implementation)
