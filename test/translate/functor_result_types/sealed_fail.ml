module type Argument = sig
  type t
end

module Actual = struct
  type t = int
end

module First_view : Argument = Actual
module Second_view : Argument = Actual

module Make (X : Argument) = struct
  type t = Value of int
end

module First = Make (First_view)
module Second = Make (Second_view)

let incorrect (x : First.t) : Second.t = x
