type 'a t = 'a list Atomic.t

exception Empty

let create () = Atomic.make []

let rec push t value =
  let before = Atomic.get t in
  if not (Atomic.compare_and_set t before (value :: before)) then push t value

(* Linearizes at the read that finds the stack empty, by raising. *)
let rec pop_exn t =
  match Atomic.get t with
  | [] -> raise Empty
  | hd :: tail as before -> if Atomic.compare_and_set t before tail then hd else pop_exn t
