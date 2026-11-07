module type TAG = sig end

module Tag = struct end
module OtherTag = struct end

module Make (Tag : TAG) = struct
  let read (cell : 'a Atomic.t) = Atomic.get cell
  (*@ Ghost.scope (fun step ->
      let token = Read.bind () in
      Read.access token cell expected;
      let result = step () in
      Read.commit token cell expected result result;
      result) *)
  (*@ Ghost.returns (fun result () -> result) *)
  (*@ manual *)
  (*@ result, [seen : 'a] = atomic read [expected : 'a] cell
      atomic requires own cell expected
      atomic ensures own cell expected && result === seen && seen === expected *)
end

module First = Make (Tag)
module Again = Make (Tag)
module Alias = First
module Other = Make (OtherTag)

let both (integer : int Atomic.t) (boolean : bool Atomic.t) =
  let first =
    First.read integer
    (*@ Ghost.scope (fun invoke ->
        let (result, seen) = invoke 17 in
        assert (result === seen);
        result) *)
  in
  let again =
    Again.read boolean
    (*@ Ghost.scope (fun invoke ->
        let (result, seen) = invoke true in
        assert (result === seen);
        result) *)
  in
  let alias =
    Alias.read integer
    (*@ Ghost.scope (fun invoke ->
        let (result, seen) = invoke 17 in
        assert (result === seen);
        result) *)
  in
  let other =
    Other.read boolean
    (*@ Ghost.scope (fun invoke ->
        let (result, seen) = invoke true in
        assert (result === seen);
        result) *)
  in
  (first, again, alias, other)
(*@ manual *)
(*@ result = both integer boolean
    requires own integer 17 && own boolean true
    ensures own integer 17 && own boolean true && result === (17, true, 17, true) *)
