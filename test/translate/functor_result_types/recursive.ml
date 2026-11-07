module type Argument = sig end

module Argument = struct end

module Make (X : Argument) = struct
  type t = End | Next of t
  type wrapper = { root : t }

  let identity (x : t) = x
  (*@ result = identity x ensures result = x *)

  let wrapper_identity (x : wrapper) = x
  (*@ result = wrapper_identity x ensures result = x *)
end

module Left = Make (Argument)
module Right = Make (Argument)

let recursive () =
  match Right.identity (Left.Next Left.End) with
  | Right.Next Right.End -> ()
  | Right.End | Right.Next (Right.Next _) -> assert false

let payload () =
  let x = Right.wrapper_identity { Left.root = Left.Next Left.End } in
  match x.Right.root with
  | Right.Next Right.End -> ()
  | Right.End | Right.Next (Right.Next _) -> assert false
