module type Argument = sig end

module A = struct end
module B = struct end
module C = struct end

module Make (X : Argument) (Y : Argument) = struct
  type t = Value of int
end

module With_A = Make (A)
module First = With_A (B)
module Second = With_A (C)

let incorrect (x : First.t) : Second.t = x
