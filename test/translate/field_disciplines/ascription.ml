module type Input = sig
  type t = { mutable counter : int [@caravan.frozen] }
end

module Actual : Input = struct
  type t = { mutable counter : int }
end

module Use (X : Input) = struct
  let id (value : int) = value
end

module Result = Use (Actual)

module type Reexport = sig
  type t = Actual.t = { mutable counter : int }
end

module Reexported : Reexport = Actual

module Hidden : sig
  type t
end =
  Actual
