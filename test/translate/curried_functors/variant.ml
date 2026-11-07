module type Argument = sig end

module A = struct end
module B = struct end
module B_alias = B

module Make (X : Argument) (Y : Argument) = struct
  type t = Empty | Value of int

  let identity (x : t) = x
  (*@ result = identity x ensures result = x *)
end

module Make_alias = Make
module Direct = Make (A) (B)
module Repeated = Make (A) (B)
module With_A = Make (A)
module With_A_alias = With_A
module Partial = With_A (B)
module Aliased = With_A_alias (B_alias)
module Via_functor = Make_alias (A) (B)

let direct (x : Make(A)(B).t) = Direct.identity x
(*@ result = direct x ensures result = x *)

let check () =
  let x = Repeated.identity (Direct.Value 7) in
  let x = Partial.identity x in
  let x = Aliased.identity x in
  let x = Via_functor.identity (direct x) in
  match x with Direct.Value n -> assert (n = 7) | Direct.Empty -> assert false
