(* Saturn's Treiber stack. *)

type 'a t = 'a list Atomic.t

let create () = Atomic.make_contended []
let of_list list = Atomic.make_contended list
let is_empty t = Atomic.get t == []

let rec push t value backoff =
  let before = Atomic.get t in
  let after = value :: before in
  if not (Atomic.compare_and_set t before after) then push t value (Backoff.once backoff)

let push t value = push t value Backoff.default

exception Empty

type ('a, _) poly = Option : ('a, 'a option) poly | Value : ('a, 'a) poly

let peek_as : type a r. a t -> (a, r) poly -> r =
 fun t poly ->
  match Atomic.get t with
  | [] ->
      begin match poly with Option -> None | Value -> raise Empty
      end
  | hd :: _ -> ( match poly with Option -> Some hd | Value -> hd)

let peek_exn t = peek_as t Value
let peek_opt t = peek_as t Option

type ('a, _) poly2 =
  | Option : ('a, 'a option) poly2
  | Value : ('a, 'a) poly2
  | Unit : ('a, unit) poly2

let rec pop_as : type a r. a t -> Backoff.t -> (a, r) poly2 -> r =
 fun t backoff poly ->
  match Atomic.get t with
  | [] ->
      begin match poly with Option -> None | Value | Unit -> raise Empty
      end
  | hd :: tail as before ->
      if Atomic.compare_and_set t before tail then
        match poly with Option -> Some hd | Value -> hd | Unit -> ()
      else pop_as t (Backoff.once backoff) poly

let pop_exn t = pop_as t Backoff.default Value
let pop_opt t = pop_as t Backoff.default Option
let drop_exn t = pop_as t Backoff.default Unit

let rec pop_all t backoff =
  match Atomic.get t with
  | [] -> []
  | old_head ->
      if Atomic.compare_and_set t old_head [] then old_head
      else pop_all t (Backoff.once backoff)

let pop_all t = pop_all t Backoff.default
