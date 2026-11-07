module type View = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)

  val read : t -> int
  (*@ result = read x
      requires counter x state
      ensures counter x state && result = state *)
end

module Left : View = Actual.First
module Right : View = Actual.First

let client (x : Left.t) = Left.read x
(*@ result = client x
    requires Right.counter x state
    ensures Left.counter x state && result = state *)
