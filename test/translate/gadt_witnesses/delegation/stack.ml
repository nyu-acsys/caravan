(* A wrapper delegating its atomic update to an atomic function with its own contract. *)

type 'a t = 'a list Atomic.t

let create () = Atomic.make []

let rec take t =
  match Atomic.get t with
  | [] -> None
  | hd :: tail as before ->
      if Atomic.compare_and_set t before tail then Some hd else take t
(*@ r = atomic take t
    atomic requires stack t xs
    atomic ensures match xs with [] -> r = None && stack t [] | x :: xs' -> r === Some x && stack t xs' *)

let pop_opt t = take t
