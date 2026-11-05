type 'a t

(*@ predicate cell (c : 'a t) (value [@implicit] : 'a) *)

val skip : int t -> unit
(*@ atomic skip c
    atomic requires cell c before
    atomic ensures cell c before *)

val set_unit : unit t -> bool
(*@ result = atomic set_unit c
    atomic requires cell c ()
    atomic ensures cell c () && result *)
