  $ caravan --shh stdlib_list.ml stdlib_list.ml
  Verification successful.
  Verification successful.

  $ caravan --shh --emit-rav stdlib_list.ml > stdlib_list.rav
  $ raven --shh --typeonly stdlib_list.rav
  Verification successful.

Unsupported members remain unsupported even though OCaml can type-check them.

  $ echo 'let tail (values : int list) = List.tl values' > stdlib_list_unsupported.ml
  $ caravan --shh stdlib_list_unsupported.ml
  [Error] File "stdlib_list_unsupported.ml", line 1, columns 31-45:
  1 | let tail (values : int list) = List.tl values
                                     ^^^^^^^^^^^^^^
  Unsupported Error: A call of Stdlib__List.tl is not supported yet.
  [1]
