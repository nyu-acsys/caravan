module type Argument = sig end

module Argument = struct end
module Argument_alias = Argument

module Make (X : Argument) = struct
  type t = Empty | Value of int

  let identity (x : t) = x
  (*@ result = identity x ensures result = x *)
end

module Make_alias = Make
module Left = Make (Argument)
module Right = Make (Argument)
module Via_argument = Make (Argument_alias)
module Via_functor = Make_alias (Argument)
module Result_alias = Left

let check () =
  let x = Right.identity (Left.Value 7) in
  let x = Via_argument.identity x in
  let x = Via_functor.identity x in
  let x = Result_alias.identity x in
  match x with Right.Value n -> assert (n = 7) | Right.Empty -> assert false
