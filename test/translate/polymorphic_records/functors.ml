module Make () = struct
  type 'a t = { mutable contents : 'a option }

  let make value = { contents = value }
  (*@ cell = make value ensures own cell.contents value *)

  let write cell value = cell.contents <- value
  (*@ write cell value
      requires own cell.contents before
      ensures own cell.contents value *)

  let read { contents } = contents
  (*@ result = read cell
      requires own cell.contents value
      ensures own cell.contents value && result === value *)
end

module First = Make ()
module Second = Make ()

let clients () =
  let first = First.make None in
  First.write first (Some 42);
  assert (First.read first = Some 42);
  let second = Second.make None in
  Second.write second (Some true);
  assert (Second.read second = Some true)

module type Element = sig
  type t
end

module Nested (A : Element) = struct
  type 'a t = { mutable payload : A.t * 'a list; label : A.t }

  let make label values = { payload = (label, values); label }

  (*@ cell = make label values ensures own cell.payload (label, values) && own cell.label label *)
  let get cell = cell.payload
  (*@ result = get cell requires own cell.payload stored
      ensures own cell.payload stored && result === stored *)
end

module Int = struct
  type t = int
end

module Bool = struct
  type t = bool
end

module Int_record = Nested (Int)
module Int_alias = Nested (Int)
module Bool_record = Nested (Bool)

let nested () =
  let first = Int_record.make 7 [ true ] in
  let second = Bool_record.make true [ 8 ] in
  assert (Int_alias.get first = (7, [ true ]));
  assert (Bool_record.get second = (true, [ 8 ]))
