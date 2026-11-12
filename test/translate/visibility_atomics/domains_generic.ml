type 'a cell = { mutable value : 'a [@caravan.frozen] }

let allocate value = { value }
(*@ result = allocate value
    ensures own ~writer:Ghost.self result.value value *)

let create value = allocate value
(*@ Ghost.scope (fun step ->
    let cell = step () in
    Value.freeze cell;
    cell) *)
(*@ manual *)
(*@ result = create value ensures Value.visible Ghost.self result value *)

let read (cell : 'a cell) = cell.value
(*@ Ghost.frozen_scope (fun load -> let result = load () in result) *)
(*@ manual *)
(*@ result = read cell
    requires Value.visible Ghost.self cell value
    ensures Value.visible Ghost.self cell value && result === value *)

let run value =
  let cell = create value in
  let reader = Domain.spawn (fun () -> read cell) in
  let first = Domain.join reader in
  let factory = Domain.spawn (fun () -> create first) in
  let returned = Domain.join factory in
  read returned
(*@ result = run value ensures result === value *)

let client () =
  assert (run 17 = 17);
  assert (run true)

module type Element = sig
  type t
end

module Worker (A : Element) = struct
  let work (cell : A.t cell) = read cell
  (*@ result = work cell
      requires Value.visible Ghost.self cell value
      ensures Value.visible Ghost.self cell value && result === value *)

  let run (value : A.t) =
    let cell = create value in
    let domain = Domain.spawn (fun () -> work cell) in
    Domain.join domain
  (*@ result = run value ensures result === value *)
end

module Int = struct
  type t = int
end

module Bool = struct
  type t = bool
end

module First = Worker (Int)
module Second = Worker (Bool)

let functor_client () =
  assert (First.run 23 = 23);
  assert (Second.run true)
