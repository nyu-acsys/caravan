module Cell = struct
  let read (cell : int Atomic.t) = Atomic.get cell
  (*@ Ghost.scope (fun step -> let observed = step () in observed) *)
  (*@ manual *)
  (*@ result = read cell
      requires own cell value
      ensures own cell value && result = value *)

  let forward cell = read cell
  (*@ Ghost.scope (fun invoke -> let result = invoke () in result) *)
  (*@ manual *)
  (*@ result = forward cell
      requires own cell value
      ensures own cell value && result = value *)
end

let client cell = Cell.forward cell
(*@ result = client cell
    requires own cell value
    ensures own cell value && result = value *)
