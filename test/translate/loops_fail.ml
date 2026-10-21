(* An invariant that does not hold at the start, one that is not maintained, and a
   result the invariant does not give. *)

let start_wrong n =
  let s = ref 0 in
  for _ = 1 to n do
    (*@ invariant own s.contents v && v = 1 *)
    s := 1
  done
(*@ start_wrong n
    requires n >= 0 *)

let not_kept n =
  let c = ref 0 in
  while !c < n do
    (*@ invariant own c.contents k && k <= 0 *)
    incr c
  done
(*@ not_kept n
    requires 0 <= n <= 1000 *)

let too_weak n =
  let c = ref 0 in
  while !c < n do
    (*@ invariant own c.contents k && 0 <= k *)
    incr c
  done;
  !c
(*@ r = too_weak n
    requires 0 <= n <= 1000
    ensures r = n *)
