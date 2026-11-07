module Definition = struct
  type tag = bool
end

module type CELL = sig
  type tag = int
  type 'a t

  (*@ invariant is_cell (q : 'a t) *)
  (*@ predicate cell (q : 'a t) (value : 'a * tag) *)

  val create : 'a -> 'a t
  (*@ q = create value ensures is_cell q && cell q (value, 0) *)
end

module Cell : CELL = struct
  type tag = int
  type 'a t = ('a * tag) Atomic.t

  let create value = Atomic.make (value, 0)
  (*@ initially { value = (value, 0); tag = true } *)
end

let integer () = Cell.create 17
(*@ q = integer () ensures Cell.is_cell q && Cell.cell q (17, 0) *)

let boolean () = Cell.create true
(*@ q = boolean () ensures Cell.is_cell q && Cell.cell q (true, 0) *)
