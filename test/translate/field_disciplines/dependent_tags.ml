module type Input = sig
  type t = { mutable counter : int [@caravan.frozen] }
end

module Make
    (A : Input)
    (B : sig
      type t = A.t = { mutable counter : int [@caravan.frozen] }
    end) =
struct
  let id (value : int) = value
end

module Actual : Input = struct
  type t = { mutable counter : int }
end

module Partial = Make (Actual)
module Result = Partial (Actual)

module Fresh () = struct
  type t = { mutable counter : int [@caravan.frozen] }
end

module Fresh_actual = Fresh ()
module Other_partial = Make (Fresh_actual)
module Other = Other_partial (Fresh_actual)
