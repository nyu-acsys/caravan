module Make () = struct
  type ('a, _) node =
    | Null : ('a, [> `Null ]) node
    | Node : { mutable value : 'a } -> ('a, [> `Node ]) node

  and 'a link = Link : ('a, [< `Null | `Node ]) node -> 'a link [@@unboxed]

  let local value =
    let node = Node { value } in
    let saved = Link node in
    assert (Link node == saved);
    match node with
    | Node record ->
        record.value <- value;
        record.value
  (*@ result = local value ensures result === value *)
end

module First = Make ()
module Second = Make ()

let clients () =
  assert (First.local 42 = 42);
  assert (Second.local true)
