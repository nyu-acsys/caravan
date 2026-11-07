type t
(*@ invariant is_counter (c : t) *)
(*@ predicate model (c : t) (value [@implicit] : R.t) *)
(*@ predicate other (c : t) (value [@implicit] : R.t) *)

val create : unit -> t
(*@ c = create () ensures is_counter c && model c R.invalid && other c (R.excl 2) *)

val set_one : t -> unit
(*@ atomic set_one c requires is_counter c
    atomic requires model c R.invalid && other c (R.excl 2)
    atomic ensures model c (R.excl 1) && other c (R.excl 3) *)

val read : t -> int
(*@ result = atomic read c requires is_counter c
    atomic requires model c (R.excl 1) && other c (R.excl 3)
    atomic ensures model c (R.excl 1) && other c (R.excl 3) && result = 1 *)

val exercise : unit -> int
(*@ result = exercise () ensures result = 1 *)
