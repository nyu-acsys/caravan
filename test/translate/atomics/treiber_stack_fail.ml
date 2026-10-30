(* Treiber's stack with bugs, against the contracts in treiber_stack_fail.mli. *)

type t = int list Atomic.t

let create () = Atomic.make []
(*@ fold stack t [] *)

(* The test is the wrong way around. *)
let is_empty t = Atomic.get t (*@ commit *) != []

(* The value is not pushed. *)
let rec push t value =
  let before = Atomic.get t in
  if not (Atomic.compare_and_set t before before) then push t value

let rec pop_opt t =
  match Atomic.get t (*@ returning [] -> commit *) with
  | [] -> None
  | hd :: tail as before ->
      if Atomic.compare_and_set t before tail then Some hd else pop_opt t

let rec pop_all t =
  match Atomic.get t (*@ returning [] -> commit *) with
  | [] -> []
  | old_head -> if Atomic.compare_and_set t old_head [] then old_head else pop_all t
