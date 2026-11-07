type 'a box = Empty | Box of 'a
type ('a, 'b) pair = Pair of 'a * 'b
type 'a record = { contents : 'a; enabled : bool }
type 'a tree = Leaf | Node of 'a * 'a tree list
type 'a phantom = Phantom
type 'a a_outer = Outer of 'a box list

let wrap value = Box value
(*@ result = wrap value pure ensures result === Box value *)

let get box = match box with Empty -> None | Box value -> Some value
(*@ result = get box pure
    ensures match box with Empty -> result === None | Box value -> result === Some value *)

let pair left right = Pair (left, right)
(*@ result = pair left right pure ensures result === Pair (left, right) *)

let first value = match value with Pair (left, _) -> left
(*@ result = first value pure
    ensures match value with Pair (left, _) -> result === left *)

let record contents = { contents; enabled = true }
(*@ result = record contents pure ensures result.contents === contents && result.enabled *)

let project value = value.contents
(*@ result = project value pure ensures result === value.contents *)

let project_pair pair = match pair with value, _ -> value.contents
(*@ result = project_pair pair pure
    ensures match pair with value, _ -> result === value.contents *)

let outer value = Outer [ Box value ]
(*@ result = outer value pure ensures result === Outer [ Box value ] *)

let leaf () : 'a tree = Leaf
(*@ result = leaf () pure ensures result === Leaf *)

let node value children = Node (value, children)
(*@ result = node value children pure ensures result === Node (value, children) *)

let root = function Leaf -> None | Node (value, _) -> Some value
(*@ result = root tree pure
    ensures match tree with Leaf -> result === None | Node (value, _) -> result === Some value *)

let phantom () : 'a phantom = Phantom
(*@ result = phantom () pure ensures result === Phantom *)

let integers () =
  assert (get (wrap 17) = Some 17);
  assert (first (pair 17 true) = 17);
  assert (project (record 23) = 23);
  assert (root (node 17 [ leaf () ]) = Some 17)

let booleans () =
  assert (get (wrap true) = Some true);
  assert (first (pair false 17) = false);
  assert (project (record true));
  assert (root (node true [ node false [] ]) = Some true)

let phantom_client () =
  let (_ : int phantom) = phantom () in
  let (_ : bool phantom) = phantom () in
  ()

type 'a void = |

let absurd (value : 'a void) : 'b = match value with _ -> .
(*@ result = absurd value pure ensures false *)

let storage_roundtrip value =
  let cell = Atomic.make (Box value) in
  match Atomic.get cell with Empty -> value | Box result -> result
(*@ result = storage_roundtrip value ensures result === value *)

let storage_clients () =
  assert (storage_roundtrip 17 = 17);
  assert (storage_roundtrip true)

let bounded (tree : int tree) = match tree with Leaf -> 0 | Node (value, _) -> value
(*@ result = bounded tree ensures result <= max_int && result >= min_int *)
