(** Trusted contracts for the supported subset of [Stdlib.List]. *)

val rev : 'a list -> 'a list
(*@ result = rev xs pure
    ensures result === (match xs with
      | [] -> []
      | head :: tail -> rev tail @ [head]) *)

val rev_append : 'a list -> 'a list -> 'a list
(*@ result = rev_append xs ys pure
    ensures result === rev xs @ ys *)
