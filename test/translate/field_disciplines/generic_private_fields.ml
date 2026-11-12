module type X = sig
  type 'a t = { mutable value : 'a [@caravan.frozen] }
end

module Generic (X : X) = struct
  let allocate value : 'a X.t = { value }
  (*@ cell = allocate value ensures own ~writer:Ghost.self cell.value value *)

  let write_then_read (cell : 'a X.t) value =
    cell.value <- value;
    cell.value
  (*@ result = write_then_read cell value
      requires own ~writer:Ghost.self cell.value previous
      ensures own ~writer:Ghost.self cell.value value && result === value *)
end

module Actual = struct
  type 'a t = { mutable value : 'a [@caravan.frozen] }
end

module Client = Generic (Actual)

let clients () =
  let integers = Client.allocate 17 in
  assert (Client.write_then_read integers 42 = 42);
  let booleans = Client.allocate false in
  assert (Client.write_then_read booleans true)

module Fresh () = struct
  type t = { mutable count : int [@caravan.frozen] }

  let allocate count = { count }
  (*@ cell = allocate count ensures own ~writer:Ghost.self cell.count count *)

  let check value =
    let cell = { count = value } in
    cell.count
  (*@ result = check value ensures result === value *)
end

module Instance = Fresh ()

let fresh_client value =
  let cell = Instance.allocate value in
  cell.count <- value;
  assert (Instance.check value = value);
  cell.count
(*@ result = fresh_client value ensures result === value *)

module type Cell = sig
  type t = { mutable count : int [@caravan.frozen] }

  val update : t -> int -> int
  (*@ result = update cell value
      requires own ~writer:Ghost.self cell.count previous
      ensures own ~writer:Ghost.self cell.count value && result === value *)
end

module Implementation : Cell = struct
  type t = { mutable count : int }

  let update cell value =
    cell.count <- value;
    cell.count
end

module Forward (Cell : Cell) = struct
  let update cell value = Cell.update cell value
  (*@ result = update cell value
      requires own ~writer:Ghost.self cell.count previous
      ensures own ~writer:Ghost.self cell.count value && result === value *)
end

module Forwarded = Forward (Implementation)

let forwarded_client value =
  let cell = { Implementation.count = value } in
  Forwarded.update cell value
(*@ result = forwarded_client value ensures result === value *)
