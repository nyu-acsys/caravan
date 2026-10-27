module type Argument = sig end

module Argument = struct end
module Other_argument = struct end

module Make (X : Argument) = struct
  type item = { value : int }
  type chain = End | Link of item * chain
  type cell = { mutable value : int }

  let pack value : item = { value }
  (*@ result = pack value ensures result.value = value *)

  let unpack (item : item) = item.value
  (*@ result = unpack item ensures result = item.value *)

  let create value = { value }
  (*@ result = create value ensures own result.value value *)

  let read cell = cell.value
  (*@ result = read cell requires own cell.value value
      ensures own cell.value value && result = value *)

  let write cell value = cell.value <- value
  (*@ write cell value requires own cell.value previous ensures own cell.value value *)

  let prepend item chain = Link (item, chain)
  (*@ result = prepend item chain ensures result = Link (item, chain) *)
end

module First = Make (Argument)
module Alias = Make
module Again = Alias (Argument)
module Other = Make (Other_argument)

let roundtrip value = Again.unpack (First.pack value)
(*@ result = roundtrip value ensures result = value *)

let allocated value =
  let cell = First.create value in
  Again.write cell value;
  First.read cell
(*@ result = allocated value ensures result = value *)
