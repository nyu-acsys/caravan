module type Reader = sig
  val read : 'a Atomic.t -> 'a
  (*@ result = read [@atomic] cell
      requires own cell value
      ensures own cell value && result === value *)
end

module Native = struct
  let read cell = Atomic.get cell
  (*@ result = read [@atomic] cell
      requires own cell value
      ensures own cell value && result === value *)
end

module Make (R : Reader) = struct
  let read cell = R.read cell
  (*@ result = read [@atomic] cell
      requires own cell value
      ensures own cell value && result === value *)
end

module Instance = Make (Native)

let read (cell : int Atomic.t) = Instance.read cell
(*@ Ghost.scope (fun read ->
    unfold shared cell;
    let result = read () in
    fold shared cell;
    result) *)
(*@ manual *)
(*@ result = read cell requires shared cell ensures shared cell && result = 6 *)
