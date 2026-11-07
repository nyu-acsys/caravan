module type S = sig
  type 'a t

  (*@ predicate stack (st : 'a t) (xs [@implicit] : 'a list) *)
  val create : unit -> 'a t
  (*@ result = create () ensures stack result [] *)

  val push : 'a t -> 'a -> unit
  (*@ atomic push st value
      atomic requires stack st xs
      atomic ensures stack st (value :: xs) *)

  val pop : 'a t -> 'a option
  (*@ result = atomic pop st
      atomic requires stack st xs
      atomic ensures match xs with
        | [] -> result === None && stack st []
        | value :: rest -> result === Some value && stack st rest *)
end
