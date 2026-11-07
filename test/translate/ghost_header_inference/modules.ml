module Make () : sig
  type 'a t = { cell : 'a Atomic.t }

  val read : 'a t -> 'a
  (*@ result = read owner
      requires own owner.cell value
      ensures own owner.cell value && result === value *)
end = struct
  type 'a t = { cell : 'a Atomic.t }

  let read owner =
    let helper cell = if cell == owner.cell then Atomic.get cell else Atomic.get cell in
    helper owner.cell
end

module First = Make ()
module Second = Make ()
