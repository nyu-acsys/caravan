type cell = { mutable value : int [@caravan.relaxed] }

let allocate value = { value }
(*@ result = allocate value
    ensures exists event : Ghost.t.
      Value.state result value (Set.singleton (event, value)) *)

let read (cell : cell) = cell.value
(*@ result = read cell
    requires Value.state cell current writes
    ensures Value.state cell current writes &&
      (exists event : Ghost.t. Value.observed cell event result && Set.mem (event, result) writes) *)

let write (cell : cell) value = cell.value <- value
(*@ write cell value
    requires Value.state cell current writes
    ensures exists event : Ghost.t.
      Value.state cell value (Set.union writes (Set.singleton (event, value))) &&
      Value.observed cell event value *)

let initial value =
  let cell = allocate value in
  read cell
(*@ result = initial value ensures result === value *)
