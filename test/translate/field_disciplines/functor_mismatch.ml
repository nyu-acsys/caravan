module type Ordinary = sig
  type t = { mutable counter : int }
end

module type Input = sig
  include Ordinary
end

module Use (X : Input) = struct
  let id (value : X.t) = value
end

module Actual = struct
  type t = { mutable counter : int [@caravan.frozen] }
end

module Result = Use (Actual)
