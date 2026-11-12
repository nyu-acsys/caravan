type ('a, _) node =
  | Null : ('a, [> `Null ]) node
  | Node : {
      next : 'a link Atomic.t;
      mutable value : 'a;
      mutable capacity : int;
      mutable counter : int;
    }
      -> ('a, [> `Node ]) node

and 'a link = Link : ('a, [< `Null | `Node ]) node -> 'a link [@@unboxed]

let local (value : int) =
  let node = Node { next = Atomic.make (Link Null); value; capacity = 2; counter = 0 } in
  let saved = Link node in
  let (Link restored) = saved in
  assert (Link restored == saved);
  match node with
  | Node record ->
      record.capacity <- record.capacity - 1;
      record.counter <- 1;
      assert (record.capacity = 1 && record.counter = 1);
      let cell = Atomic.make (Link Null) in
      assert (Atomic.compare_and_set cell (Link Null) saved);
      assert (Atomic.get cell == saved);
      record.value
(*@ result = local value ensures result === value *)

let separate () =
  let first =
    Node { next = Atomic.make (Link Null); value = 1; capacity = 0; counter = 0 }
  in
  let second =
    Node { next = Atomic.make (Link Null); value = 1; capacity = 0; counter = 0 }
  in
  assert (first != second);
  assert (Link first != Link second)

let read (node : ('a, [ `Node ]) node) = match node with Node record -> record.value
(*@ result = read node
    requires contents node value
    ensures contents node value && result === value *)

let write (Node record : ('a, [ `Node ]) node) value = record.value <- value
(*@ write node value
    requires contents node before
    ensures contents node value *)

let as_node (Link node) : (_, [< `Node ]) node =
  match node with Null -> assert false | Node _ as node -> node
(*@ result = as_node link
    requires match link with Link Null -> false | Link (Node _) -> true
    ensures Link result === link *)
