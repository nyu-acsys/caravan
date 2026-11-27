A list segment over an element predicate provides the iterated predicate, the list
with a hole at an index, and lemmas that take an element out and put it back.

  $ caravan --shh cells.ml
  Verification successful.

  $ caravan --shh --emit-rav cells.ml > cells.rav
  $ raven --shh --typeonly cells.rav
  Verification successful.

The element must be the one at the exposed index.

  $ caravan --shh wrong_index.ml
  [Error] File "wrong_index.mlp", line 7, columns 2-34:
  7 |   cells_expose cells 0 0 (k + 1) c;
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: A precondition may not hold for this call.
  File "wrong_index.mlp", line 4, columns 0-31:
  4 | list_segment cells over cell_at
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [Error] File "wrong_index.mlp", line 8, columns 9-47:
  8 |   unfold cell_at k c (cells_suffix cells 0 k) 0;
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Failed to unfold predicate. The predicate may not hold at this point.
  File "wrong_index.mlp", line 8, columns 9-47:
  8 |   unfold cell_at k c (cells_suffix cells 0 k) 0;
               ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This predicate may not hold.
  [1]

The element predicate must be declared before the segment, with the position, the
element and the list after it as its first parameters.

  $ caravan --shh missing.ml
  [Error] File "missing.mlp", line 1, columns 24-31:
  1 | list_segment cells over cell_at
                              ^^^^^^^
  Syntax Error: The element predicate of a list segment must be declared before it.
  [1]

  $ caravan --shh shape.ml
  [Error] File "shape.mlp", line 3, columns 0-31:
  3 | list_segment cells over cell_at
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Syntax Error: The third parameter of a list segment's element predicate must be the list after the element, a list of the element's type.
  [1]

  $ caravan --shh keyword.ml
  [Error] File "keyword.mlp", line 3, columns 19-24:
  3 | list_segment cells under cell_at
                         ^^^^^
  Syntax Error: Expected list_segment name over predicate.
  [1]
