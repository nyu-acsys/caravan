module type Input = sig
  type t = { mutable counter : int }
end

module Alias : Input = Attributed
