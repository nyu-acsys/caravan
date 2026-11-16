(*@ invariant live (cell : int Atomic.t) *)
val read : int Atomic.t -> int [@@caravan.opens []]
(*@ result = read cell
    opens { live cell }
    requires live cell
    ensures live cell *)
