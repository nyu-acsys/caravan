type 'a items = 'a list
type ('a, 'b) pair = 'a * 'b
type 'a nested = ('a items, bool) pair option
type 'a cell = 'a Atomic.t

let identity (items : 'a items) = items
(*@ result = identity items pure ensures result === items *)

let nested (value : 'a nested) = value
(*@ result = nested value pure ensures result === value *)

let integers (value : int items) = identity value
(*@ result = integers value ensures result === value *)

let booleans (value : bool items) = identity value
(*@ result = booleans value ensures result === value *)

let nested_integers (value : int nested) = nested value
(*@ result = nested_integers value ensures result === value *)

let create (value : int items) : int items cell = Atomic.make value
(*@ result = create value ensures own result value *)

let read (cell : int items cell) = Atomic.get cell
(*@ result = read cell
    requires own cell items
    ensures own cell items && result === items *)

type 'a phantom = int
type ('a, 'phantom) retained = 'a list * 'phantom phantom

let phantom_identity (value : 'a phantom) = value
(*@ result = phantom_identity value pure ensures result === value *)

let retained_identity (value : ('a, 'phantom) retained) = value
(*@ result = retained_identity value pure ensures result === value *)

let phantom_client () = phantom_identity 17
(*@ result = phantom_client () ensures result === 17 *)

let retained_client (items : bool list) = retained_identity (items, 23)
(*@ result = retained_client items ensures result === (items, 23) *)

let mathematical_client () = ()
(*@ mathematical_client ()
    ensures forall value : integer. identity [value] === [value] *)

module Payload = struct
  type 'a t = 'a list

  let create (value : 'a t) = Atomic.make value
  (*@ cell = create value ensures own cell value *)

  let read (cell : 'a t Atomic.t) = Atomic.get cell
  (*@ result = read cell
      requires own cell value
      ensures own cell value && result === value *)
end

module Alias = Payload

let scoped_client () =
  let cell = Payload.create [ true ] in
  assert (Alias.read cell = [ true ])
