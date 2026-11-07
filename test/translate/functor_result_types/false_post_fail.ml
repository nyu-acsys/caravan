module type Argument = sig end

module Argument = struct end

module Make (X : Argument) = struct
  type t = Value of int

  let identity (x : t) = x
  (*@ result = identity x ensures result = x *)
end

module Left = Make (Argument)
module Right = Make (Argument)

let incorrect () = Right.identity (Left.Value 7)
(*@ result = incorrect () ensures result = Left.Value 8 *)
