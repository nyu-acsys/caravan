exception Stop of int

(* The raises clause does not hold where the loop raises. *)
let first_over a n =
  let i = ref 0 in
  while !i < n do
    (*@ invariant own i.contents k && 0 <= k && k <= a + 1 *)
    if !i > a then raise (Stop !i);
    incr i
  done;
  !i
(*@ r = first_over a n
    requires 0 <= a && a < n && n < 1000
    raises Stop k -> k = a *)
