module type View = sig
  type t

  (*@ predicate counter (x : t) (n [@implicit] : int) *)
  val read : t -> int
  (*@ result = read x requires counter x state
      ensures counter x state && result = state *)
end

module Make (Cell : View) = struct
  type item = { cell : Cell.t }
  type link = Wrap of item
  type box = { mutable contents : Cell.t }

  let pack cell : item = { cell }
  (*@ result = pack cell ensures result.cell === cell *)

  let unpack (item : item) = item.cell
  (*@ result = unpack item ensures result === item.cell *)

  let read (item : item) = Cell.read item.cell
  (*@ result = read item requires Cell.counter item.cell state
      ensures Cell.counter item.cell state && result = state *)

  let create cell = { contents = cell }
  (*@ result = create cell ensures own result.contents cell *)

  let get box = box.contents
  (*@ result = get box requires own box.contents cell
      ensures own box.contents cell && result === cell *)
end

module First = Make (Actual.First)
module Again = Make (Actual.First)
module Second = Make (Actual.Second)

type enclosing = Enclose of First.item
type enclosing_cell = { mutable item : First.item }

let client cell =
  let item = First.pack cell in
  let same = Again.unpack item in
  let boxed = Again.create same in
  let unpacked = First.get boxed in
  Again.read (First.pack unpacked)
(*@ result = client cell requires Actual.First.counter cell state
    ensures Actual.First.counter cell state && result = state *)
