(*@ invariant zero (cell : int Atomic.t) *)

val read : int Atomic.t -> int [@@caravan.opens []]
(*@ result = read cell
    requires zero cell
    ensures zero cell && result = 0 *)
