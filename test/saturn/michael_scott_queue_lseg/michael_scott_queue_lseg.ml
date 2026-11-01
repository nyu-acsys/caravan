(** Michael-Scott queue with an explicit segment proof. *)
type node = Nil | Next of int * node Atomic.t

type t = { head : node Atomic.t Atomic.t; tail : node Atomic.t Atomic.t }

let create () =
  let next = Atomic.make Nil in
  let head = Atomic.make_contended next in
  let tail = Atomic.make_contended next in
  { head; tail }

let rec fix_tail tail new_tail =
  let old_tail = Atomic.get tail in
  if Atomic.get new_tail == Nil && not (Atomic.compare_and_set tail old_tail new_tail)
  then fix_tail tail new_tail

let push { tail; _ } value =
  let rec find_tail_and_enq curr_end node =
    if not (Atomic.compare_and_set curr_end Nil node) then
      match Atomic.get curr_end with
      | Nil -> find_tail_and_enq curr_end node
      | Next (_, n) -> find_tail_and_enq n node
  in
  let new_tail = Atomic.make Nil in
  let newnode = Next (value, new_tail) in
  let old_tail = Atomic.get tail in
  if not (Atomic.compare_and_set old_tail Nil newnode) then
    begin match Atomic.get old_tail with
    | Nil -> find_tail_and_enq old_tail newnode
    | Next (_, n) -> find_tail_and_enq n newnode
    end;
  if not (Atomic.compare_and_set tail old_tail new_tail) then fix_tail tail new_tail

let rec pop_as q backoff =
  let old_head = Atomic.get q.head in
  match Atomic.get old_head with
  | Nil -> None
  | Next (value, next) ->
      if Atomic.compare_and_set q.head old_head next then Some value
      else
        let backoff = Backoff.once backoff in
        pop_as q backoff

let pop_opt q = pop_as q Backoff.default
let is_empty { head; _ } = Atomic.get (Atomic.get head) == Nil

let of_list list =
  let tail_ = Atomic.make Nil in
  let tail = Atomic.make_contended tail_ in
  let rec build_next = function
    | [] -> tail_
    | hd :: tl -> Atomic.make @@ Next (hd, build_next tl)
  in
  let head = Atomic.make_contended @@ build_next list in
  { head; tail }
