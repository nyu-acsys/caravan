let work (cell : int ref) =
  cell := 1;
  7
(*@ result = work cell
    requires own cell.contents 0
    ensures own cell.contents 1 && result === 7 *)

let launch cell = Domain.spawn (fun () -> work cell)
(*@ domain = launch cell
    requires own cell.contents 0
    ensures Job.handle domain cell *)

let finish (domain : int Domain.t) (cell : int ref) = Domain.join domain
(*@ result = finish domain cell
    requires Job.handle domain cell
    ensures own cell.contents 1 && result === 7 *)

let client () =
  let cell = ref 0 in
  let domain = launch cell in
  let alias = domain in
  let result = finish alias cell in
  assert (!cell = 1);
  result
(*@ result = client () ensures result === 7 *)

let reverse () =
  let first = ref 0 in
  let second = ref 0 in
  let left = Domain.spawn (fun () -> work first) in
  let right = Domain.spawn (fun () -> work second) in
  let y = Domain.join right in
  let x = Domain.join left in
  assert (!first = 1 && !second = 1);
  x + y
(*@ result = reverse () ensures result === 14 *)

let unit_work () = 3
(*@ result = unit_work () ensures result === 3 *)

let named () =
  let domain = Domain.spawn unit_work in
  Domain.join domain
(*@ result = named () ensures result === 3 *)

let other (cell : int ref) =
  cell := 2;
  9
(*@ result = other cell
    requires own cell.contents 0
    ensures own cell.contents 2 && result === 9 *)

let distinct () =
  let first = ref 0 in
  let second = ref 0 in
  let left = Domain.spawn (fun () -> work first) in
  let right = Domain.spawn (fun () -> other second) in
  let alias = left in
  let y = Domain.join right in
  let x = Domain.join alias in
  assert (!first = 1 && !second = 2);
  x + y
(*@ result = distinct () ensures result === 16 *)

let unit_result (cell : int ref) = cell := 4
(*@ unit_result cell
    requires own cell.contents 0
    ensures own cell.contents 4 *)

let void () =
  let cell = ref 0 in
  let domain = Domain.spawn (fun () -> unit_result cell) in
  Domain.join domain;
  !cell
(*@ result = void () ensures result === 4 *)

module Domain = struct
  let spawn value = value + 1
  (*@ result = spawn value
      requires value === 0
      ensures result === 1 *)
end

let shadow () = Domain.spawn 0
(*@ result = shadow () ensures result === 1 *)
