module type Argument = sig
  type t
end

module Actual = struct
  type t = int
end

module First_view : sig
  module Arg : Argument
  module Alias = Arg
end = struct
  module Arg = Actual
  module Alias = Arg
end

module Second_view : sig
  module Arg : Argument
end = struct
  module Arg = Actual
end

module Exposed_view : sig
  module Arg = Actual
end = struct
  module Arg = Actual
end

module Make (X : Argument) = struct
  type value = Value of int
  type cell = { mutable contents : int }

  let identity (x : value) = x
  (*@ result = identity x ensures result = x *)
end

module First = Make (First_view.Arg)
module Repeated = Make (First_view.Arg)
module Internal_alias = Make (First_view.Alias)
module Second = Make (Second_view.Arg)
module Direct = Make (Actual)
module Exposed = Make (Exposed_view.Arg)

let check () =
  let first = { First.contents = 0 } in
  let second = { Second.contents = 1 } in
  let direct = { Direct.contents = 2 } in
  first.Repeated.contents <- 7;
  direct.Exposed.contents <- 9;
  assert (first.Internal_alias.contents = 7);
  assert (second.Second.contents = 1);
  assert (direct.Direct.contents = 9);
  match Internal_alias.identity (Repeated.identity (First.Value 7)) with
  | First.Value x -> assert (x = 7)

let exposed () =
  match Exposed.identity (Direct.Value 9) with Direct.Value x -> assert (x = 9)
