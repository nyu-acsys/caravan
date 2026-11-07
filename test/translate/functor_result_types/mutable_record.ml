module type Argument = sig end

module Argument = struct end

module Make (X : Argument) = struct
  type t = { mutable value : int }

  let read (x : t) = x.value
  (*@ result = read x requires own x.value n ensures own x.value n && result = n *)

  let write (x : t) n = x.value <- n
  (*@ write x n requires own x.value old_value ensures own x.value n *)
end

module Left = Make (Argument)
module Right = Make (Argument)

let check () =
  let x = { Left.value = 0 } in
  let y = { Right.value = 1 } in
  Right.write x 7;
  assert (Left.read x = 7);
  assert (Left.read y = 1)
