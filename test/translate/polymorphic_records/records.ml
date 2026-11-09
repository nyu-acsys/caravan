type 'a cell = { mutable value : 'a }
type 'a alias = 'a cell

let make value = { value }
(*@ cell = make value ensures own cell.value value *)

let read cell = cell.value
(*@ result = read cell
    requires own cell.value value
    ensures own cell.value value && result === value *)

let write cell value = cell.value <- value
(*@ write cell value
    requires own cell.value before
    ensures own cell.value value *)

let pattern ({ value } : 'a alias) = value
(*@ result = pattern cell
    requires own ~fraction:Permission.half cell.value value
    ensures own ~fraction:Permission.half cell.value value && result === value *)

let match_alias (cell : 'a alias) =
  match cell with
  | { value } as same ->
      same.value <- value;
      value
(*@ result = match_alias cell
    requires own cell.value value
    ensures own cell.value value && result === value *)

let integer (cell : int cell) = cell.value
(*@ result = integer cell
    requires own cell.value value
    ensures own cell.value value && result = value *)

let clients () =
  let integers = make 17 in
  write integers 42;
  assert (integer integers = 42);
  assert (read integers = 42);
  assert (pattern integers = 42);
  assert (match_alias integers = 42);
  let booleans = make false in
  write booleans true;
  assert (read booleans);
  assert (pattern booleans);
  assert (match_alias booleans)

type ('a, 'b) pair = { mutable left : 'a; mutable right : 'b; tag : int }

let pair left right tag = { left; right; tag }
(*@ cell = pair left right tag
    ensures own cell.left left && own cell.right right && own cell.tag tag *)

let replace_left cell value = cell.left <- value
(*@ replace_left cell value
    requires own cell.left before && own cell.right right && own cell.tag tag
    ensures own cell.left value && own cell.right right && own cell.tag tag *)

let read_pair { left; right; tag } = (left, right, tag)
(*@ result = read_pair cell
    requires own cell.left left && own cell.right right && own cell.tag tag
    ensures own cell.left left && own cell.right right && own cell.tag tag
    ensures result === (left, right, tag) *)

let pairs () =
  let first = pair 1 false 7 in
  replace_left first 2;
  assert (read_pair first = (2, false, 7));
  let second = pair true 3 8 in
  replace_left second false;
  assert (read_pair second = (false, 3, 8))

type 'a other = { mutable other_value : 'a }

let independent value replacement =
  let first = make value in
  let second = { other_value = value } in
  write first replacement;
  second.other_value
(*@ result = independent value replacement ensures result === value *)

type 'a node = { mutable payload : 'a; mutable next : 'a node option }

let node payload next = { payload; next }
(*@ cell = node payload next
    ensures own cell.payload payload && own cell.next next *)

let link cell next = cell.next <- next
(*@ link cell next requires own cell.next before ensures own cell.next next *)

let next cell = cell.next
(*@ result = next cell
    requires own cell.next successor
    ensures own cell.next successor && result === successor *)

let recursive () =
  let tail = node false None in
  let head = node true None in
  link head (Some tail);
  match next head with None -> assert false | Some cell -> assert (cell == tail)

type 'a phantom = { mutable count : int }

let phantom value = { count = value }
(*@ cell = phantom value ensures own cell.count value *)

let phantom_read (cell : 'a phantom) = cell.count
(*@ result = phantom_read cell
    requires own cell.count value
    ensures own cell.count value && result = value *)

let phantom_clients () =
  let first : int phantom = phantom 1 in
  let second : bool phantom = phantom 2 in
  first.count <- 3;
  assert (phantom_read first = 3);
  assert (phantom_read second = 2)

type 'a stack = { mutable contents : 'a list; mutex : Mutex.t; condition : Condition.t }

let stack () = { contents = []; mutex = Mutex.create (); condition = Condition.create () }
(*@ cell = stack () ensures own cell.contents [] && own cell.mutex mutex &&
    own cell.condition condition *)

let push cell value = cell.contents <- value :: cell.contents
(*@ push cell value requires own cell.contents values
    ensures own cell.contents (value :: values) *)

let contents cell = cell.contents
(*@ result = contents cell requires own cell.contents values
    ensures own cell.contents values && result === values *)

let stack_clients () =
  let first = stack () in
  push first 17;
  push first 42;
  assert (contents first = [ 42; 17 ]);
  let second = stack () in
  push second false;
  assert (contents second = [ false ])

let identity (cell : 'a cell) = cell == cell
(*@ result = identity cell ensures result *)

let physical () =
  let first = make 17 in
  let second = make 17 in
  assert (not (first == second));
  let current = Atomic.make first in
  assert (Atomic.compare_and_set current first second);
  assert (Atomic.get current == second)

let phantom_shared () =
  let shared = { count = 0 } in
  let integer : int phantom = shared in
  let boolean : bool phantom = shared in
  integer.count <- 42;
  assert (phantom_read boolean = 42)
