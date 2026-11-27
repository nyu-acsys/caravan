type 'a cell = { mutable value : 'a [@caravan.relaxed] }

let allocate value = { value }
(*@ result = allocate value
    ensures exists event : Ghost.t.
      Value.state result value (Set.singleton (event, value)) *)

let read (cell : 'a cell) = cell.value
(*@ result = read cell
    requires Value.state cell current writes
    ensures Value.state cell current writes &&
      (exists event : Ghost.t. Value.observed cell event result && Set.mem (event, result) writes) *)

let traced (cell : 'a cell) = cell.value
(*@ Ghost.scope (fun load ->
    let value = load () in
    let (_event, _entries) = Value.snapshot cell in
    let event = Value.observe cell value in
    Value.duplicate cell event value;
    Value.reconcile cell event value;
    value) *)
(*@ manual *)
(*@ result = traced cell
    requires Value.state cell current writes
    ensures Value.state cell current writes &&
      (exists event : Ghost.t. Value.observed cell event result && Set.mem (event, result) writes) *)

let client value = read (allocate value)
(*@ result = client value ensures result === value *)

module type Storage = sig
  type t
end

module Make (Storage : Storage) = struct
  type cell = { mutable value : Storage.t [@caravan.relaxed] }

  let allocate value = { value }
  (*@ result = allocate value
      ensures exists event : Ghost.t.
        Item.state result value (Set.singleton (event, value)) *)

  let read (cell : cell) = cell.value
  (*@ result = read cell
      requires Item.state cell current writes
      ensures Item.state cell current writes &&
        (exists event : Ghost.t. Item.observed cell event result && Set.mem (event, result) writes) *)

  let client value = read (allocate value)
  (*@ result = client value ensures result === value *)
end

module Int = struct
  type t = int
end

module Integers = Make (Int)

let concrete value = Integers.client value
(*@ result = concrete value ensures result === value *)
