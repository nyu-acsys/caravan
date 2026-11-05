module type S = sig
  type t

  (*@ predicate holds (cell : t) (value [@implicit] : int) *)
  (*@ invariant shared (cell : t) *)

  val create : int -> t
  (*@ cell = create value ensures holds cell value && shared cell *)

  val ordinary : t -> int
  (*@ result = ordinary cell
      requires holds cell value
      ensures holds cell value && result = value *)

  val read_atomic : t -> int
  (*@ result = atomic read_atomic cell
      requires shared cell
      ensures shared cell
      atomic requires holds cell value
      atomic ensures holds cell value && result = value *)
end
