module type Argument = sig end

module First_argument = struct end
module Second_argument = struct end

module Make (X : Argument) = struct
  type t = Value of int
end

module First = Make (First_argument)
module Second = Make (Second_argument)

let incorrect (x : First.t) : Second.t = x
