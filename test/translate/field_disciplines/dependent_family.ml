module type Arg = sig
  type t
end

module Arg = struct
  type t = int
end

module Make (A : Arg) = struct
  type t = { mutable value : A.t [@caravan.frozen] }
end

module Left = Make (Arg)
