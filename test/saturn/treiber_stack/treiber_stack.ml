(* Saturn's Treiber stack, of integers. *)

type t = int list Atomic.t

let create () = Atomic.make []
(*@ fold stack t [] *)

let of_list list = Atomic.make_contended list
(*@ fold stack t list *)

let is_empty t = Atomic.get t (*@ commit *) == []

let rec push t value backoff =
  let before = Atomic.get t in
  let after = value :: before in
  if not (Atomic.compare_and_set t before after) then push t value (Backoff.once backoff)

let push t value = push t value Backoff.default

let rec pop_opt t =
  match Atomic.get t (*@ returning [] -> commit *) with
  | [] -> None
  | hd :: tail as before ->
      if Atomic.compare_and_set t before tail then Some hd else pop_opt t

let rec pop_all t backoff =
  match Atomic.get t (*@ returning [] -> commit *) with
  | [] -> []
  | old_head ->
      if Atomic.compare_and_set t old_head [] then old_head
      else pop_all t (Backoff.once backoff)

let pop_all t = pop_all t Backoff.default
