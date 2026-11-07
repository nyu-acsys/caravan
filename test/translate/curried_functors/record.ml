module type Argument = sig end

module A = struct end
module B = struct end
module B_alias = B

module Make (X : Argument) (Y : Argument) = struct
  type t = { value : int }

  let identity (x : t) = x
  (*@ result = identity x ensures result = x *)
end

module Direct = Make (A) (B)
module Repeated = Make (A) (B)
module With_A = Make (A)
module With_A_alias = With_A
module Partial = With_A (B)
module Aliased = With_A_alias (B_alias)

let check () =
  let x = Repeated.identity { Direct.value = 7 } in
  let x = Partial.identity x in
  let x = Aliased.identity x in
  assert (x.Direct.value = 7)
