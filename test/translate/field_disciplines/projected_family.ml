module type Arg = sig end

module Arg = struct end

module type S = sig
  type t = { mutable value : int [@caravan.frozen] }
end

module Make (A : Arg) : S = struct
  type t = { mutable value : int }
end

module Left = Make (Arg)
