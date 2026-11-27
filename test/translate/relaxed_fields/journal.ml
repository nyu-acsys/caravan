type cell = { mutable value : int [@caravan.relaxed] }

let read (cell : cell) = cell.value
(*@ Ghost.scope (fun load ->
    let (current_event, before) = Value.snapshot cell in
    let result = load () in
    let event = Value.observe cell result in
    Value.duplicate cell event result;
    Value.reconcile cell event result;
    assert (Set.mem (event, result) before);
    result) *)
(*@ manual *)
(*@ result = read cell
    requires Value.state cell current writes
    ensures Value.state cell current writes &&
      (exists event : Ghost.t. Value.observed cell event result && Set.mem (event, result) writes) *)

let read_nonnegative (cell : cell) = cell.value
(*@ Ghost.scope (fun load ->
    unpack cell current writes;
    let result = load () in
    let event = Value.observe cell result in
    Value.reconcile cell event result;
    assert (result >= 0);
    pack cell current writes;
    result) *)
(*@ manual *)
(*@ result = read_nonnegative cell
    requires safe cell current writes
    ensures safe cell current writes && result >= 0 *)

let write_nonnegative (cell : cell) value = cell.value <- value
(*@ Ghost.scope (fun store ->
    unpack cell current writes;
    let result = store () in
    let event = Value.observe cell value in
    pack cell value (Set.union writes (Set.singleton (event, value)));
    result) *)
(*@ manual *)
(*@ write_nonnegative cell value
    requires safe cell current writes && value >= 0
    ensures exists event : Ghost.t.
      safe cell value (Set.union writes (Set.singleton (event, value))) &&
      Value.observed cell event value *)

let shared_read (cell : cell) = cell.value
(*@ Ghost.scope (fun load ->
    let (current, writes) = unfold nonnegative cell {current; writes} in
    unpack cell current writes;
    let result = load () in
    let event = Value.observe cell result in
    Value.reconcile cell event result;
    assert (result >= 0);
    pack cell current writes;
    fold nonnegative cell {current = current; writes = writes};
    result) *)
(*@ manual *)
(*@ result = shared_read cell
    requires nonnegative cell
    ensures nonnegative cell && result >= 0 *)

let shared_write (cell : cell) value = cell.value <- value
(*@ Ghost.scope (fun store ->
    let (current, writes) = unfold nonnegative cell {current; writes} in
    unpack cell current writes;
    let result = store () in
    let event = Value.observe cell value in
    let updated = Set.union writes (Set.singleton (event, value)) in
    pack cell value updated;
    fold nonnegative cell {current = value; writes = updated};
    result) *)
(*@ manual *)
(*@ shared_write cell value
    requires nonnegative cell && value >= 0
    ensures nonnegative cell *)
