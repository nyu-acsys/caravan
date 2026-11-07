module type CELL = sig
  type t
end

module Make (Cell : CELL) = struct
  type t = Cell.t

  let identity (cell : t) = cell
end

module First = Make (Actual.First)
module Second = Make (Actual.Second)
module Alias = First
module Repeated = Make (Actual.First)
module Arg_alias = Actual.First
module Functor_alias = Make
module Via_alias = Functor_alias (Arg_alias)

module Group = struct
  module Nested = Make (Actual.First)
end

module Hidden_first : sig
  type t = Actual.First.t
end =
  Make (Actual.First)
