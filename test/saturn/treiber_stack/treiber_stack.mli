(** Treiber's lock-free stack, after Saturn's. *)

type 'a t

(*@ predicate stack (t : 'a t) (xs [@implicit] : 'a list) *)

val create : unit -> 'a t
(*@ t = create ()
    ensures stack t [] *)

val of_list : 'a list -> 'a t
(*@ t = of_list xs
    ensures stack t xs *)

val is_empty : 'a t -> bool
(*@ b = atomic is_empty t
    atomic requires stack t xs
    atomic ensures b = (xs = []) && stack t xs *)

val push : 'a t -> 'a -> unit
(*@ atomic push t v
    atomic requires stack t xs
    atomic ensures stack t (v :: xs) *)

val push_all : 'a t -> 'a list -> unit
(*@ atomic push_all t values
    atomic requires stack t xs
    atomic ensures stack t (List.rev values @ xs) *)

exception Empty

val peek_opt : 'a t -> 'a option
(*@ r = atomic peek_opt t
    atomic requires stack t xs
    atomic ensures stack t xs && match xs with [] -> r = None | x :: _ -> r === Some x *)

val peek_exn : 'a t -> 'a
(*@ r = atomic peek_exn t
    atomic requires stack t xs
    atomic ensures stack t xs && match xs with [] -> false | x :: _ -> r === x
    atomic raises Empty -> xs = [] && stack t [] *)

val pop_exn : 'a t -> 'a
(*@ r = atomic pop_exn t
    atomic requires stack t xs
    atomic ensures match xs with [] -> false | x :: xs' -> r === x && stack t xs'
    atomic raises Empty -> xs = [] && stack t [] *)

val drop_exn : 'a t -> unit
(*@ atomic drop_exn t
    atomic requires stack t xs
    atomic ensures match xs with [] -> false | _ :: xs' -> stack t xs'
    atomic raises Empty -> xs = [] && stack t [] *)

val pop_opt : 'a t -> 'a option
(*@ r = atomic pop_opt t
    atomic requires stack t xs
    atomic ensures match xs with
      | [] -> r = None && stack t []
      | x :: xs' -> r === Some x && stack t xs' *)

val pop_all : 'a t -> 'a list
(*@ r = atomic pop_all t
    atomic requires stack t xs
    atomic ensures r === xs && stack t [] *)
