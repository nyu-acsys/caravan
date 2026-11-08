type t = int Atomic.t

let remember (root : t) (cell : t) = ()
(*@ remember root cell
    requires live root
    requires past (mem cell s.cells)
    ensures live root
    ensures past (mem cell s.cells) *)

let launch (root : t) (cell : t) = Domain.spawn (fun () -> remember root cell)
(*@ domain = launch root cell
    requires live root
    requires past (mem cell s.cells)
    ensures Remember.handle domain root cell *)

let finish (domain : unit Domain.t) (root : t) (cell : t) =
  Domain.join domain;
  remember root cell
(*@ manual *)
(*@ finish domain root cell
    requires Remember.handle domain root cell
    requires live root
    ensures live root
    ensures past (mem cell s.cells) *)

let client (root : t) (cell : t) =
  let domain = launch root cell in
  finish domain root cell
(*@ client root cell
    requires live root
    requires past (mem cell s.cells)
    ensures live root *)

let supplied (root : t) (cell : t) =
  let domain = Domain.spawn (fun () -> remember root cell) in
  Domain.join domain;
  remember root cell
(*@ supplied root cell
    requires live root
    requires past (mem cell s.cells)
    ensures live root
    ensures past (mem cell s.cells) *)
