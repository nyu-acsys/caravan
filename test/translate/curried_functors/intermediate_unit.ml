module type Argument = sig end

module A = struct end
module B = struct end

module Make (X : Argument) () (Y : Argument) = struct
  type t = Value of int

  let identity (x : t) = x
  (*@ result = identity x ensures result = x *)
end

module With_A = Make (A)
module Fresh_scope = With_A ()
module Fresh_scope_alias = Fresh_scope
module First = Fresh_scope (B)
module Repeated = Fresh_scope_alias (B)

let check () =
  match Repeated.identity (First.Value 7) with First.Value n -> assert (n = 7)
