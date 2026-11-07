module type Argument = sig end

module Argument = struct end

module Make (X : Argument) = struct
  type t = Value of int

  let incorrect (x : t) = x
  (*@ result = incorrect x ensures result = Value 0 *)
end

module Left = Make (Argument)
module Right = Make (Argument)
