type cell = { mutable value : int [@caravan.frozen] }

let allocate value = { value }

(*@ result = allocate value ensures own ~writer:Ghost.self result.value value *)
let create value = allocate value
(*@ Ghost.scope (fun make -> let cell = make () in Value.freeze cell;cell) *)
(*@ manual *)
(*@ result = create value ensures Value.visible Ghost.self result value *)

let initialize (cell : cell) = Mutex.create ()
(*@ Ghost.scope (fun make ->
    fold Payload.resource Ghost.self cell;
    let mutex = make () in
    Guard.initialize mutex Ghost.self cell;
    mutex) *)
(*@ manual *)
(*@ result = initialize cell requires (Ghost.Mutex.context self held && Value.visible Ghost.self cell 0)
    ensures Guard.is_mutex result cell && Value.frozen cell 0 && not (Finset.mem result held) *)

let read (mutex : Mutex.t) cell =
  Mutex.lock mutex
  (*@ Ghost.scope (fun lock -> let result = lock () in
      unfold Payload.resource Ghost.self cell;result) *);
  let result =
    cell.value
    (*@ Ghost.frozen_scope (fun load -> let result = load () in result) *)
  in
  Mutex.unlock mutex
  (*@ Ghost.scope (fun unlock -> fold Payload.resource Ghost.self cell;
      let result = unlock () in result) *);
  result
(*@ manual *)
(*@ result = read mutex cell requires (Ghost.Mutex.context self held && not (Finset.mem mutex held) && Guard.is_mutex mutex cell && Value.frozen cell 0) ensures result === 0 *)

let client () =
  let cell = create 0 in
  let mutex = initialize cell in
  read mutex cell
(*@ result = client () ensures result === 0 *)

let try_read (mutex : Mutex.t) cell =
  if
    Mutex.try_lock mutex
    (*@ Ghost.scope (fun acquire -> let success = acquire () in
         if success then unfold Payload.resource Ghost.self cell else ();
         success) *)
  then (
    let value =
      cell.value
      (*@ Ghost.frozen_scope (fun load -> let result = load () in result) *)
    in
    Mutex.unlock mutex
    (*@ Ghost.scope (fun release -> fold Payload.resource Ghost.self cell;
        let result = release () in result) *);
    value)
  else 0
(*@ manual *)
(*@ result = try_read mutex cell
    requires (Guard.is_mutex mutex cell && Value.frozen cell 0)
    ensures result === 0 *)

let wait_read (mutex : Mutex.t) condition cell =
  Mutex.lock mutex
  (*@ Ghost.scope (fun acquire -> let result = acquire () in
      unfold Payload.resource Ghost.self cell;result) *);
  Condition.wait condition mutex
  (*@ Ghost.scope (fun suspend -> fold Payload.resource Ghost.self cell;
      let result = suspend () in unfold Payload.resource Ghost.self cell;result) *);
  let value =
    cell.value
    (*@ Ghost.frozen_scope (fun load -> let result = load () in result) *)
  in
  Condition.signal condition;
  Condition.broadcast condition;
  Mutex.unlock mutex
  (*@ Ghost.scope (fun release -> fold Payload.resource Ghost.self cell;
      let result = release () in result) *);
  value
(*@ manual *)
(*@ result = wait_read mutex condition cell
    requires (Ghost.Mutex.context self held && not (Finset.mem mutex held) &&
      Guard.is_mutex mutex cell && Guard.is_condition condition mutex && Value.frozen cell 0)
    ensures result === 0 *)
