module type Reader = sig
  val read : int Atomic.t -> int
  (*@ result = read [@atomic] cell
      requires own cell value
      ensures own cell value && result = value *)
end

module Ordinary = struct
  let read (cell : int Atomic.t) = Atomic.get cell
  (*@ result = read cell
      requires own cell value
      ensures own cell value && result = value *)
end

module Make (R : Reader) = struct
  let read cell = R.read cell
end

module Instance = Make (Ordinary)
