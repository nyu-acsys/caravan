exception Stop of int

(* The loop's raises clause does not hold where it raises. *)
let count_until a n =
  let i = ref 0 in
  (try
     while !i < n do
       (*@ invariant own i.contents k && 0 <= k && k <= a
           raises Stop m -> own i.contents a && m = a + 1 *)
       if !i = a then raise (Stop !i);
       incr i
     done
   with Stop _ -> ());
  !i
(*@ r = count_until a n
    requires 0 <= a && a < n && n < 1000 *)
