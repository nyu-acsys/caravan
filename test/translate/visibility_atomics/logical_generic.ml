type unused = { mutable frozen : int [@caravan.frozen] }

module type INPUT = sig
  val identity : int -> int
  (*@ result = identity value ensures result = value *)
end

module A = struct
  let identity (value : int) = value
  (*@ result = identity value ensures result = value *)
end

module Make (X : INPUT) = struct
  let read (cell : int Atomic.t) =
    let result =
      Atomic.get cell
      (*@ Ghost.scope (fun step ->
      let token = Read.bind () in
      preserve_pending token cell;
      let value = Read.access token cell in
      unfold contents cell value;
      let result = step () in
      fold contents cell value;
      Read.commit token cell result;
      preserve_committed token cell result;
      result) *)
    in
    X.identity result
  (*@ manual *)
  (*@ result = atomic read cell
      atomic requires contents cell value
      atomic ensures contents cell value && result = value *)
end

module One = Make (A)
module Again = Make (A)
module Alias = One

let use_one cell = One.read cell
(*@ result = use_one cell
    requires contents cell value
    ensures contents cell value && result = value *)

let use_again cell = Again.read cell
(*@ result = use_again cell
    requires contents cell value
    ensures contents cell value && result = value *)

let use_alias cell = Alias.read cell
(*@ result = use_alias cell
    requires contents cell value
    ensures contents cell value && result = value *)
