exception Stop of int
exception Negative

(* Raising out of a while loop: what the raises clause says holds where it raises. *)
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
    ensures r = n
    raises Stop k -> k = a + 1 *)

let check n = if n < 0 then raise Negative else n
(*@ r = check n
    ensures r = n
    raises Negative -> n < 0 *)

(* A for loop calling a function that may raise. *)
let checks n =
  for j = -1 to n do
    let _ = check j in
    ()
  done
(*@ checks n
    requires 0 <= n && n < 1000
    raises Negative -> true *)

(* A loop inside a handler: its raises clause says what holds when it raises. *)
let count_until a n =
  let i = ref 0 in
  (try
     while !i < n do
       (*@ invariant own i.contents k && 0 <= k && k <= a
           raises Stop m -> own i.contents a && m = a *)
       if !i = a then raise (Stop !i);
       incr i
     done
   with Stop _ -> ());
  !i
(*@ r = count_until a n
    requires 0 <= a && a < n && n < 1000
    ensures r = a *)
