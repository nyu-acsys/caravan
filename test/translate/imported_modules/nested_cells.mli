module type Cell = sig
  type t

  (*@ predicate holds (cell : t) (value : int) *)

  val make : int -> t
  (*@ cell = make value ensures holds cell value *)

  val read : t -> int
  (*@ result = read cell
      requires holds cell value
      ensures holds cell value && result = value *)
end

module type Atomic_cell = sig
  type t

  (*@ invariant shared (cell : t) *)
  (*@ predicate holds (cell : t) (value [@implicit] : int) *)
  (*@ predicate ticket (cell : t) (count : int) *)

  val make : int -> t
  (*@ cell = make value
      ensures shared cell && holds cell value && ticket cell 0 *)

  val read : t -> int
  (*@ result = atomic read cell
      requires shared cell && ticket cell count
      ensures ticket cell count
      atomic requires holds cell value
      atomic ensures holds cell value && result = value *)

  val replace : t -> int -> unit
  (*@ atomic replace cell value
      requires shared cell && ticket cell count
      ensures ticket cell count
      atomic requires holds cell previous
      atomic ensures holds cell value *)
end

module Ordinary : Cell
module Alias = Ordinary

module Nested : sig
  module Other : Cell
  module Alias = Other
  module Atomic : Atomic_cell
  module Other_atomic : Atomic_cell
end
