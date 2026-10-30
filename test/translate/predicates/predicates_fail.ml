(* A predicate that is not folded, and one folded where its body does not hold. *)

type counter = { mutable count : int }

(*@ predicate valid (c : counter) (n : int) = own c.count n && 0 <= n <= 1000 *)

let make () = { count = 0 }
(*@ c = make ()
    ensures valid c 0 *)

let set c v = c.count <- v
(*@ set c v
    requires valid c n
    ensures valid c v *)
(*@ fold valid c v *)
