type 'a t = 'a Atomic.t

let create value = Atomic.make value
(*@ initially { value = value; cells = [] } *)

let remember (root : 'a t) (cell : 'a t) = ()
let forward (root : 'a t) (cell : 'a t) = remember root cell
let integers (root : int t) (cell : int t) = forward root cell
let booleans (root : bool t) (cell : bool t) = forward root cell

let mixed (left : int t) (left_cell : int t) (right : bool t) (right_cell : bool t) =
  remember left left_cell;
  remember right right_cell
