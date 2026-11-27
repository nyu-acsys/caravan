module type Input = sig
  type t = { mutable counter : int [@caravan.frozen] }
  type u = t = { mutable counter : int }
end

module Make (X : Input) = struct
  let id (value : int) = value
end

module Actual : Input = struct
  type t = { mutable counter : int }
  type u = t = { mutable counter : int }
end

module Result = Make (Actual)
