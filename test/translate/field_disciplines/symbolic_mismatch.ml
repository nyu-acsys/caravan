module type Input = sig
  type t = { mutable counter : int [@caravan.frozen] }
end

module Make
    (A : Input)
    (B : sig
      type t = A.t = { mutable counter : int [@caravan.relaxed] }
    end) =
struct
  let id (value : int) = value
end
