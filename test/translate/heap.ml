(* Mutable records and ref cells are references, with a Raven field per OCaml field;
   contracts own them. *)

type counter = { mutable count : int; step : int }

let create s = { count = 0; step = s }
(*@ c = create s
    ensures own c.count 0 && own c.step s *)

let tick c = c.count <- c.count + c.step
(*@ tick c
    requires own c.count n && own c.step s
    requires 0 <= n && 0 <= s && n + s <= max_int
    ensures own c.count (n + s) && own c.step s *)

let twice () =
  let c = create 3 in
  tick c;
  tick c;
  c.count
(*@ r = twice ()
    ensures r = 6 *)

let swap (a : int ref) b =
  let t = !a in
  a := !b;
  b := t
(*@ swap a b
    requires own a.contents x && own b.contents y
    ensures own a.contents y && own b.contents x *)

let bump r = incr r
(*@ bump r
    requires own r.contents n && n < max_int
    ensures own r.contents (n + 1) *)

(* A record without a mutable field is a value. *)
type point = { x : int; y : int }

let mirror p = { x = p.y; y = p.x }
(*@ q = mirror p
    ensures q.x = p.y && q.y = p.x *)
