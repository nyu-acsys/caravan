module type Cell = sig
  type t = { mutable value : int [@caravan.frozen] }

  val allocate : int -> t
  (*@ cell = allocate value
      ensures own ~writer:Ghost.self cell.value value *)

  val read : t -> int
  (*@ result = read cell
      requires own ~writer:Ghost.self cell.value value
      ensures own ~writer:Ghost.self cell.value value && result === value *)
end

module Implementation : Cell = struct
  type t = { mutable value : int }

  let allocate value = { value }
  let read cell = cell.value
end

module Forward (Cell : Cell) = struct
  let allocate value = Cell.allocate value
  (*@ cell = allocate value
      ensures own ~writer:Ghost.self cell.value value *)

  let read cell = Cell.read cell
  (*@ result = read cell
      requires own ~writer:Ghost.self cell.value value
      ensures own ~writer:Ghost.self cell.value value && result === value *)
end

module Client = Forward (Implementation)

let clients () =
  let integer = Client.allocate 17 in
  assert (Client.read integer = 17);
  let second = Client.allocate 23 in
  assert (Client.read second = 23)

module type Box = sig
  type 'a t = { mutable value : 'a [@caravan.frozen] }
end

module Generic (Box : Box) = struct
  let allocate value : 'a Box.t = { value }
  (*@ cell = allocate value
      ensures own ~writer:Ghost.self cell.value value *)

  let read (cell : 'a Box.t) = cell.value
  (*@ result = read cell
      requires own ~writer:Ghost.self cell.value value
      ensures own ~writer:Ghost.self cell.value value && result === value *)
end

module Boxes = struct
  type 'a t = { mutable value : 'a [@caravan.frozen] }
end

module Polymorphic = Generic (Boxes)

let polymorphic_clients () =
  let integer = Polymorphic.allocate 17 in
  assert (Polymorphic.read integer = 17);
  let boolean = Polymorphic.allocate true in
  assert (Polymorphic.read boolean)
