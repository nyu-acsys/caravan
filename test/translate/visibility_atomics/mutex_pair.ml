type ('a, 'b) cell = { left : 'a; right : 'b; mutable value : int [@caravan.frozen] }

let allocate left right value = { left; right; value }

(*@ result = allocate left right value ensures own ~writer:Ghost.self result.value value *)
let create left right value = allocate left right value
(*@ Ghost.scope (fun make -> let cell = make () in Value.freeze cell;cell) *)
(*@ manual *)
(*@ result = create left right value ensures Value.visible Ghost.self result value *)

let initialize (cell : ('a, 'b) cell) = Mutex.create ()
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
  let first = create true () 0 in
  let first_mutex = initialize first in
  let second = create () true 0 in
  let second_mutex = initialize second in
  read first_mutex first + read second_mutex second
(*@ result = client () ensures result === 0 *)
