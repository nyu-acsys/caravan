(*@ predicate held (cell : int Atomic.t Atomic.t)
      (value [@implicit] : int Atomic.t) *)

val create : unit -> int Atomic.t Atomic.t
(*@ cell = create () ensures held cell *)

val get : int Atomic.t Atomic.t -> int Atomic.t
(*@ value = get cell requires held cell ensures held cell *)
