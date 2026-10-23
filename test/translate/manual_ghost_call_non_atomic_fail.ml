let two_writes (cell : int Atomic.t) =
  Atomic.set cell 1
  (*@ Ghost.scope (fun step ->
    let result = step () in
    result) *);
  Atomic.set cell 0
(*@ Ghost.scope (fun step ->
    let result = step () in
    result) *)
(*@ Ghost.returns (fun result () -> 0) *)
(*@ manual *)
(*@ result, [witness : int] = two_writes cell
    requires own cell 0
    ensures own cell 0 && witness = 0 *)

let under_invariant (cell : int Atomic.t) = two_writes cell
(*@ Ghost.scope (fun invoke ->
    unfold zero cell;
    let (result, witness) = invoke () in
    assert (witness = 0);
    fold zero cell;
    result) *)
(*@ manual *)
(*@ result = under_invariant cell
    requires zero cell
    ensures zero cell && result = () *)
