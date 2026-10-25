module type Argument = sig
  type t
end

module Actual = struct
  type t = int
end

module First_view : sig
  module Arg : Argument
end = struct
  module Arg = Actual
end

module Second_view : sig
  module Arg : Argument
end = struct
  module Arg = Actual
end

module Make (X : Argument) = struct
  type t = Value of int
end

module First = Make (First_view.Arg)
module Second = Make (Second_view.Arg)

let incorrect (x : First.t) : Second.t = x
