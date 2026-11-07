module type Strong = sig
  type t = Actual.First.t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  val read : t -> int
  (*@ result = read x
      requires counter x state && state >= 0
      ensures counter x state && result = state *)
end

module type Narrow = sig
  type t = Actual.First.t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  val read : t -> int
  (*@ result = read x
      requires counter x state && state >= 0
      ensures counter x state && result >= 0 *)
end

module Already_strong : Strong = Actual.First
module Hidden : Narrow = Actual.First
module Readapted : Strong = Hidden
