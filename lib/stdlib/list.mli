(** Trusted contracts for the supported subset of [Stdlib.List]. *)

val rev : 'a list -> 'a list
(*@ result = rev xs pure
    ensures result === reverse xs *)

val rev_append : 'a list -> 'a list -> 'a list
(*@ result = rev_append xs ys pure
    ensures result === reverse xs @ ys *)

val to_seq : 'a list -> 'a Seq.t [@@caravan.local]
(*@ result = to_seq values
    ensures Seq.persistent result values *)

val of_seq : 'a Seq.t -> 'a list [@@caravan.opens []]
(*@ result = of_seq sequence
    requires Seq.persistent sequence values
    ensures result === values *)
