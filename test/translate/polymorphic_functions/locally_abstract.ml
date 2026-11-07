let pick : type a. a -> a -> bool -> a =
 fun left right first -> if first then left else right
(*@ r = pick left right first
    ensures r === (if first then left else right) *)

let use (n : int) = pick n 0 true
(*@ r = use n
    ensures r = n *)
