module type S = sig
  type 'a t

  (*@ predicate holds (cell : 'a t) (value [@implicit] : 'a) *)

  val create : 'a -> 'a t
  (*@ cell = create value ensures holds cell value *)

  val read : 'a t -> 'a
  (*@ result = read cell
      requires holds cell value
      ensures holds cell value && result === value *)
end
