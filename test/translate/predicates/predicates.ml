(* Predicates, and the ghost statements that fold and unfold them. *)

type counter = { mutable count : int }

(*@ predicate valid (c : counter) (n : int) = own c.count n && 0 <= n <= 1000 *)

let make () = { count = 0 }
(*@ c = make ()
    ensures valid c 0 *)
(*@ fold valid c 0 *)

let get c =
  (*@ unfold valid c n *)
  let v = c.count in
  (*@ fold valid c n *)
  v
(*@ v = get c
    requires valid c n
    ensures valid c n && v = n *)

type cell = { mutable value : int; mutable next : cell option }

(*@ predicate lseg (c : cell option) (l : int list) =
      match c with
      | None -> l = []
      | Some x ->
          match l with
          | [] -> false
          | v :: t -> own x.value v && own x.next n && lseg n t *)

let push c v =
  let x = { value = v; next = c } in
  let d = Some x in
  (*@ fold lseg d (v :: l) *)
  d
(*@ d = push c v
    requires lseg c l
    ensures lseg d (v :: l) *)

let head c =
  (*@ unfold lseg c l *)
  let v = match c with Some x -> x.value | None -> 0 in
  (*@ fold lseg c l *)
  v
(*@ v = head c
    requires lseg c l
    ensures lseg c l && (match l with x :: _ -> v = x | [] -> v = 0) *)
