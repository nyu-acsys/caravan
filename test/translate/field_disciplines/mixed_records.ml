type 'a cell = {
  next : 'a Atomic.t;
  label : int;
  mutable count : int; [@caravan.frozen]
  mutable payload : 'a; [@caravan.relaxed]
}

let make next payload = { next; label = 7; count = 0; payload }
let next cell = cell.next

let label cell =
  let { label; _ } = cell in
  label

let load cell = Atomic.get cell.next

let load_pattern cell =
  let { next; _ } = cell in
  Atomic.get next

let shared_label (cell : 'a cell) = cell.label

module type Storage = sig
  type 'a t = { next : 'a Atomic.t; mutable count : int [@caravan.frozen] }
end

module Use (Storage : Storage) = struct
  let make next : 'a Storage.t = { next; count = 0 }

  let next (cell : 'a Storage.t) =
    let { Storage.next; _ } = cell in
    next
end

module Storage = struct
  type 'a t = { next : 'a Atomic.t; mutable count : int [@caravan.frozen] }
end

module Instance = Use (Storage)

let generic_client () =
  let channel = Atomic.make 42 in
  let cell = Instance.make channel in
  Atomic.get (Instance.next cell)

type 'a node = Node of { next : 'a Atomic.t; mutable count : int [@caravan.frozen] }

let make_node next = Node { next; count = 0 }
let node_next (Node { next; _ }) = next

module Fresh () = struct
  type 'a t = { next : 'a Atomic.t; mutable count : int [@caravan.frozen] }

  let make next = { next; count = 0 }
  let next cell = cell.next
end

module First = Fresh ()
module Second = Fresh ()

let fresh_client () =
  let left = Atomic.make 17 in
  let right = Atomic.make true in
  let first = First.make left in
  let second = Second.make right in
  assert (Atomic.get (First.next first) = 17);
  Atomic.get (Second.next second)
