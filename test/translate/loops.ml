(* Loops, with invariants at the start of their bodies. Names free in an invariant are
   existentially quantified. *)

let sum_to n =
  let s = ref 0 in
  for i = 1 to n do
    (*@ invariant own s.contents v && 2 * v = (i - 1) * i *)
    s := !s + i
  done;
  !s
(*@ r = sum_to n
    requires 0 <= n <= 1000
    ensures 2 * r = n * (n + 1) *)

let count_down n =
  let c = ref n in
  while !c > 0 do
    (*@ invariant own c.contents k && 0 <= k <= n *)
    decr c
  done;
  !c
(*@ r = count_down n
    requires n >= 0
    ensures r = 0 *)

type counter = { mutable count : int }

let fill c n =
  for _ = 1 to n do
    (*@ invariant own c.count k && 0 <= k <= 1000 *)
    if c.count < 1000 then c.count <- c.count + 1
  done
(*@ fill c n
    requires own c.count k && 0 <= k <= 1000
    ensures own c.count j && 0 <= j <= 1000 *)

let length_acc (l : int list) =
  let n = ref 0 and rest = ref l in
  while !rest <> [] do
    (*@ invariant own n.contents k && own rest.contents r
        invariant k + List.length r = List.length l *)
    (match !rest with _ :: t -> rest := t | [] -> ());
    if !n < max_int then incr n
  done;
  !n
(*@ r = length_acc l
    requires List.length l < max_int
    ensures r = List.length l *)
