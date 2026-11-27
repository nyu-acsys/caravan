module type Frozen = sig
  type t = { mutable counter : int [@caravan.frozen] }
end

module Make
    (A : Frozen)
    (B : sig
      type t = A.t = { mutable counter : int }
    end) =
struct
  type t = B.t = { mutable counter : int }

  let id (value : int) = value
end

module Actual : Frozen = struct
  type t = { mutable counter : int }
end

module Partial = Make (Actual)
module Result = Partial (Actual)

type t = Result.t = { mutable counter : int }
