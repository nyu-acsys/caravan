module Make () = struct
  type t = { mutable contents : int }

  let read (x : t) = x.contents
  (*@ result = read x requires own x.contents n ensures own x.contents n && result = n *)

  let write (x : t) n = x.contents <- n
  (*@ write x n requires own x.contents old_value ensures own x.contents n *)
end

module Make_alias = Make
module First = Make ()
module Second = Make_alias ()
module Alias = First

let check () =
  let first = { First.contents = 0 } in
  let second = { Second.contents = 1 } in
  Alias.write first 7;
  Second.write second 9;
  assert (First.read first = 7);
  assert (Second.read second = 9)
