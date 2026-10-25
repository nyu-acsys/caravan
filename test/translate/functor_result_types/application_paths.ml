module type Argument = sig end

module Argument = struct end
module Argument_alias = Argument

module Make (X : Argument) = struct
  type t = Value of int

  let identity (x : t) = x
  (*@ result = identity x ensures result = x *)
end

module Make_alias = Make
module Instance = Make (Argument)

let direct (x : Make(Argument).t) = Instance.identity x
(*@ result = direct x ensures result = x *)

let aliased (x : Make_alias(Argument_alias).t) = Instance.identity x
(*@ result = aliased x ensures result = x *)

let check () =
  match aliased (direct (Instance.Value 7)) with Instance.Value n -> assert (n = 7)
