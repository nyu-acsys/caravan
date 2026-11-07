module type Cell = sig
  type 'a t

  (*@ invariant is_cell (q : 'a t) *)
  (*@ predicate cell (q : 'a t) (value : 'a list) *)

  val create : 'a list -> 'a t
  (*@ q = create value ensures is_cell q && cell q value *)

  val read : 'a t -> 'a list
  (*@ result = atomic read q
      requires is_cell q
      atomic requires cell q value
      atomic ensures cell q value && result === value *)
end
