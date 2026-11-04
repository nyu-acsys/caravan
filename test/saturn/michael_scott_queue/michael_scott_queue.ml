(* Saturn's Michael-Scott queue: creation, push and pop, and
   moving the tail on by a cell. *)

type 'a node = Nil | Next of 'a * 'a node Atomic.t
type 'a t = { head : 'a node Atomic.t Atomic.t; tail : 'a node Atomic.t Atomic.t }

let create () =
  let next = Atomic.make Nil in
  let head = Atomic.make_contended next in
  let tail = Atomic.make_contended next in
  { head; tail }
(*@ initially { cells = [ next ]; values = []; head = 0; tail = 0 } *)

let rec fix_tail tail new_tail =
  let old_tail = Atomic.get tail in
  if Atomic.get new_tail == Nil && not (Atomic.compare_and_set tail old_tail new_tail)
  then fix_tail tail new_tail
(*@ fix_tail [q : 'a t] tail new_tail
    requires is_queue q
    requires tail == q.tail
    requires past (mem new_tail s.cells) *)

let push { tail; _ } value =
  let rec find_tail_and_enq curr_end node =
    if not (Atomic.compare_and_set curr_end Nil node) then
      match Atomic.get curr_end with
      | Nil -> find_tail_and_enq curr_end node
      | Next (_, n) -> find_tail_and_enq n node
    (*@ find_tail_and_enq curr_end node
      continues push
      requires past (mem curr_end s.cells)
      requires node === Next (v, c) && own c Nil
      ensures past (mem c s.cells) *)
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

exception Empty

type ('a, _) poly =
  | Option : ('a, 'a option) poly
  | Value : ('a, 'a) poly
  | Unit : ('a, unit) poly

let rec pop_as : type a r. a node Atomic.t Atomic.t -> Backoff.t -> (a, r) poly -> r =
 fun head backoff poly ->
  let old_head = Atomic.get head in
  match Atomic.get old_head (*@ returning Nil -> commit *) with
  | Nil ->
      begin match poly with Value | Unit -> raise Empty | Option -> None
      end
  | Next (value, next) ->
      if Atomic.compare_and_set head old_head next then
        begin match poly with Value -> value | Option -> Some value | Unit -> ()
        end
      else
        let backoff = Backoff.once backoff in
        pop_as head backoff poly
(*@ r = atomic pop_as [q : 'a t] head backoff poly
    requires is_queue q
    requires head == q.head
    atomic requires queue q xs
    atomic ensures match poly with
      | Option ->
          if length xs = 0 then r = None && queue q xs
          else r === Some xs.(0) && queue q (drop 1 xs)
      | Value -> length xs > 0 && r === xs.(0) && queue q (drop 1 xs)
      | Unit -> length xs > 0 && queue q (drop 1 xs)
    atomic raises Empty ->
      (match poly with Option -> false | Value -> true | Unit -> true)
      && length xs = 0 && queue q xs *)

let pop_exn t = pop_as t.head Backoff.default Value
let pop_opt t = pop_as t.head Backoff.default Option
let drop_exn t = pop_as t.head Backoff.default Unit

(* If the head's cell is the last at the first read, the call waits for it to be linked,
   which commits the call with false; it commits with true if the cell is still the last
   at the second read. *)
let is_empty { head; _ } =
  Atomic.get
    (Atomic.get
       head
       (*@ returning c ->
          if c != s.cells.(length s.values) then commit false
          else wait in s.waiting on c *))
  (*@ returning Nil -> commit true *)
  == Nil

let of_list list =
  let tail_ = Atomic.make Nil in
  let tail = Atomic.make_contended tail_ in
  let rec build_next = function
    | [] -> tail_
    | hd :: tl -> Atomic.make @@ Next (hd, build_next tl)
    (*@ fold built_chain result tail_ xs *)
    (*@ result = build_next xs
      requires own tail_ Nil
      ensures own tail_ Nil && built_chain result tail_ xs *)
  in
  let head = Atomic.make_contended @@ build_next list in
  { head; tail }
(*@ initially
  let cell_list = expose_built_chain (Some q.head) tail_ list in
  { cells = to_sequence cell_list; values = to_sequence list;
    head = 0; tail = List.length list } *)
