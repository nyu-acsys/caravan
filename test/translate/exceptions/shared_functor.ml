(* A functor body its applications share, declaring an exception. *)

module type SOURCE = sig
  val get : int -> int
  (*@ r = get x
      ensures r = x *)
end

module Checked (S : SOURCE) = struct
  exception Zero

  let positive x = if S.get x = 0 then raise Zero else S.get x
  (*@ r = positive x
      ensures r = x && x <> 0
      raises Zero -> x = 0 *)

  let or_one x = try positive x with Zero -> 1
  (*@ r = or_one x
      ensures r = (if x = 0 then 1 else x) *)
end

module Identity = struct
  let get (x : int) = x
  (*@ r = get x
      ensures r = x *)
end

module A = Checked (Identity)
module B = Checked (Identity)

(* Each application's exceptions are its own: B's handler does not catch A's, nor A's B's. *)
let a_or x = try A.positive x with B.Zero -> 7 | A.Zero -> 0
(*@ r = a_or x
    ensures r = x *)

let b_or x = try B.positive x with A.Zero -> 7 | B.Zero -> 0
(*@ r = b_or x
    ensures r = x *)
