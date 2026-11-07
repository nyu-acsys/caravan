module type Argument = sig end

module A = struct end

module Fresh (X : Argument) () = struct
  type t = { mutable contents : int }

  let read (x : t) = x.contents
  (*@ result = read x requires own x.contents n ensures own x.contents n && result = n *)
end

module With_A = Fresh (A)
module With_A_alias = With_A
module First = Fresh (A) ()
module Second = With_A_alias ()

let check () =
  let first = { First.contents = 7 } in
  let second = { Second.contents = 9 } in
  assert (First.read first = 7);
  assert (Second.read second = 9)
