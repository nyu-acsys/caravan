module type Arg = sig end

module Arg = struct end

module Make (A : Arg) = struct
  type 'a t = { mutable value : 'a [@caravan.frozen] }
end

module Left = Make (Arg)
module Right = Make (Arg)

module Fresh () = struct
  type t = { mutable value : int [@caravan.frozen] }
end

module First = Fresh ()
module Second = Fresh ()
