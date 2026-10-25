module Outer () = struct
  module Make () = struct
    type t = { mutable contents : int }

    let read (x : t) = x.contents
    (*@ result = read x requires own x.contents n ensures own x.contents n && result = n *)
  end
end

module First_scope = Outer ()
module Second_scope = Outer ()
module First = First_scope.Make ()
module Second = Second_scope.Make ()

let check () =
  let first = { First.contents = 7 } in
  let second = { Second.contents = 9 } in
  assert (First.read first = 7);
  assert (Second.read second = 9)
