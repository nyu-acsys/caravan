type 'a owner = { cell : 'a Atomic.t }

let read cell = Atomic.get cell
(*@ result = read [owner : 'a owner] cell
    requires cell == owner.cell
    requires own owner.cell value
    ensures own owner.cell value && result === value *)

let get { cell } = read cell
(*@ result = get owner
    requires own owner.cell value
    ensures own owner.cell value && result === value *)

let read_manual cell = Atomic.get cell
let get_manual { cell } = read_manual cell
(*@ result = get_manual owner
    requires own owner.cell value
    ensures own owner.cell value && result === value *)

let read_integer cell = Atomic.get cell + 0
let get_integer { cell } = read_integer cell
(*@ result = get_integer owner
    requires own owner.cell value
    ensures own owner.cell value && result = value *)

let both (integer : int owner) (boolean : bool owner) =
  (get integer, get boolean, get_manual integer, get_manual boolean)
(*@ result = both integer boolean
    requires own integer.cell 17 && own boolean.cell true
    ensures own integer.cell 17 && own boolean.cell true
      && result === (17, true, 17, true) *)
