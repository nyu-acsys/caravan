module type Argument = sig end

module A = struct end
module B = struct end
module B_alias = B

module Make (X : Argument) (Y : Argument) = struct
  type t = { mutable contents : int }

  let read (x : t) = x.contents
  (*@ result = read x requires own x.contents n ensures own x.contents n && result = n *)

  let write (x : t) n = x.contents <- n
  (*@ write x n requires own x.contents old_value ensures own x.contents n *)
end

module Direct = Make (A) (B)
module Repeated = Make (A) (B)
module With_A = Make (A)
module With_A_alias = With_A
module Partial = With_A (B)
module Aliased = With_A_alias (B_alias)

let check () =
  let x = { Direct.contents = 0 } in
  Repeated.write x 7;
  assert (Partial.read x = 7);
  Aliased.write x 9;
  assert (Direct.read x = 9)
