module type Element = sig
  type t
end

module Worker (A : Element) = struct
  type cell = { tag : A.t; mutable value : int [@caravan.frozen] }

  let allocate tag value = { tag; value }
  (*@ result = allocate tag value ensures own ~writer:Ghost.self result.value value *)

  let create tag value = allocate tag value
  (*@ Ghost.scope (fun make -> let cell = make () in Value.freeze cell; cell) *)
  (*@ manual *)
  (*@ result = create tag value ensures Value.visible Ghost.self result value *)

  let initialize (cell : cell) = Mutex.create ()
  (*@ Ghost.scope (fun make ->
    fold Payload.resource Ghost.self cell;
    let mutex = make () in
    Guard.initialize mutex Ghost.self cell;
    mutex) *)
  (*@ manual *)
  (*@ result = initialize cell
    requires (Ghost.Mutex.context self held && Value.visible Ghost.self cell 0)
    ensures (Guard.is_mutex result cell && Value.frozen cell 0 && not (Finset.mem result held)) *)

  let read (mutex : Mutex.t) (cell : cell) =
    Mutex.lock mutex
    (*@ Ghost.scope (fun lock -> let result = lock () in
      unfold Payload.resource Ghost.self cell; result) *);
    let result =
      cell.value
      (*@ Ghost.frozen_scope (fun load -> let result = load () in result) *)
    in
    Mutex.unlock mutex
    (*@ Ghost.scope (fun unlock -> fold Payload.resource Ghost.self cell;
      let result = unlock () in result) *);
    result
  (*@ manual *)
  (*@ result = read mutex cell
    requires (Ghost.Mutex.context self held && not (Finset.mem mutex held) &&
      Guard.is_mutex mutex cell && Value.frozen cell 0)
    ensures result === 0 *)

  let client tag =
    let cell = create tag 0 in
    let mutex = initialize cell in
    read mutex cell
  (*@ result = client tag ensures result === 0 *)
end

module Int = struct
  type t = int
end

module Bool = struct
  type t = bool
end

module Int_worker = Worker (Int)
module Bool_worker = Worker (Bool)

let client () = Int_worker.client 0 + Bool_worker.client true
(*@ result = client () ensures result === 0 *)
