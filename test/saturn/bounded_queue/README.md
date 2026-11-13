# Saturn bounded queue

This is the constructor portion of Saturn's safe bounded queue at
[revision 50d8d9d](https://github.com/ocaml-multicore/saturn/tree/50d8d9d0a99b40434ab05bee49200cd5ffa028f5/src/bounded_queue).
It extracts the type declarations and `make_node` from
`bounded_queue.head_safe.ml`, stopping before `link_as_node`. The copyright and
license notice is retained from `bounded_queue.body.ml`.

The implementation has only Caravan field attributes: a raw relaxed payload,
a relaxed capacity cache, and a frozen counter. The proof retains counter writer
ownership so insertion can initialize it before freezing and publication.

The tests verify node allocation, including cleared dummy payloads and concrete
integer and Boolean payloads. They do not establish the complete queue proof.
Defaulted `create`, list construction, and concurrent queue operations remain
outside this extraction.
