module type View = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  (*@ predicate ticket (x : t) (n : int) *)
  val read : t -> int

  (*@ result = read x
      requires counter x state && state >= 0 && ticket x 7
      ensures counter x state && ticket x 7 && result >= 0 *)
  val touch : t -> unit
  (*@ touch x requires counter x state ensures counter x state *)
end

module Left : View = Actual.First
module Right : View = Actual.Second

let client (x : Left.t) = Left.read x
(*@ result = client x
    requires Right.counter x state && state >= 0 && Left.ticket x 7
    ensures Left.counter x state && Left.ticket x 7 && result >= 0 *)
