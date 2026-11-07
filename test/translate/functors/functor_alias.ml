module type View = sig
  val identity : int -> int
  (*@ result = identity x ensures result = x *)
end

module Make (Cell : View) = struct
  let identity x = Cell.identity x
  (*@ result = identity x ensures result = x *)
end

module Alias = Make

module Implementation = struct
  let identity (x : int) = x
  (*@ result = identity x ensures result = x *)
end

module Client = Alias (Implementation)

let identity x = Client.identity x
(*@ result = identity x ensures result = x *)
