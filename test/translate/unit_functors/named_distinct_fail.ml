module Factory () = struct
  type t = Value of int
end

module type Argument = sig
  type t
end

module Make (X : Argument) = struct
  type t = X.t
end

module First = Factory ()
module Second = Factory ()
module Left = Make (First)
module Right = Make (Second)

let incorrect (x : Left.t) : Right.t = x
