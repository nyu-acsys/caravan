module type View = sig
  type t = Actual.First.t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)

  val read : t -> int
  (*@ result = read x
      requires counter x state
      ensures counter x state && result = state *)
end

module Left : View = Actual.First
module Right : View = Actual.First

let client (x : Left.t) =
  let first = Left.read x in
  let second = Right.read x in
  assert (first = second);
  second
(*@ result = client x
    requires Left.counter x state
    ensures Right.counter x state && result = state *)
