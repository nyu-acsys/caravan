(* Reading without owning, and a wrong postcondition. *)

type counter = { mutable count : int }

let get c = c.count
(*@ v = get c *)

let reset c = c.count <- 1
(*@ reset c
    requires own c.count n
    ensures own c.count 0 *)
