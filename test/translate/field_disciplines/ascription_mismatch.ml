module type Input = sig
  type t = { mutable counter : int [@caravan.frozen] }
end

module Actual = struct
  type t = { mutable counter : int }
end

module Alias : Input = Actual
