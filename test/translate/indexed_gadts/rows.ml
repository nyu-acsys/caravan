type ('a, _) node = Null : ('a, [> `Null ]) node | Node : 'a -> ('a, [> `Node ]) node
and 'a link = Link : ('a, [< `Null | `Node ]) node -> 'a link [@@unboxed]

let make value = Node value

(*@ result = make value ensures result === Node value *)
let nullable value = Link (Node value)

(*@ result = nullable value ensures result === Link (Node value) *)
let empty () = Link Null

let roundtrip (value : int) =
  let node = make value in
  match node with Node result -> result
(*@ result = roundtrip value ensures result === value *)

let use_link (value : bool) =
  match nullable value with Link Null -> false | Link (Node result) -> result
(*@ result = use_link value ensures result === value *)

let fresh value = Node value
let tag (node : ('a, [ `Node ]) node) = match node with Node _ -> true
(*@ result = tag node ensures result *)

let inferred () =
  assert (tag (fresh 42));
  assert (tag (fresh true))

type _ tag = Empty : [> `Empty ] tag | Leaf : [> `Leaf ] tag

let leaf () = Leaf
let only_leaf (value : [ `Leaf ] tag) = match value with Leaf -> true

(*@ result = only_leaf value ensures result *)
let constant_rows () = assert (only_leaf (leaf ()))
