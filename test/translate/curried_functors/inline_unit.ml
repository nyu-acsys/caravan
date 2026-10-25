module type Argument = sig end

module A = struct end
module B = struct end

module Make (X : Argument) () (Y : Argument) = struct
  type t = { mutable contents : int }

  let read (x : t) = x.contents
  (*@ result = read x requires own x.contents n ensures own x.contents n && result = n *)
end

module First = Make (A) () (B)
module Second = Make (A) () (B)

let check () =
  let first = { First.contents = 7 } in
  let second = { Second.contents = 9 } in
  assert (First.read first = 7);
  assert (Second.read second = 9)
