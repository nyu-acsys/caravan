A singleton segment cannot claim a different stored payload.

  $ caravan --shh value_segments_bad_payload.ml
  [Error] File "value_segments_bad_payload.proof", line 23, column 7 to line 24, column 51:
  23 |   fold segment first limit [wrong] (Finset.singleton first)
              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  File "value_segments_bad_payload.proof", line 14, columns 13-43:
  14 |           && own first (Next (value, next))
                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

Its link facts must identify the node's actual successor.

  $ caravan --shh value_segments_bad_successor.ml
  [Error] File "value_segments_bad_successor.proof", line 23, column 7 to line 24, column 51:
  23 |   fold segment first limit [value] (Finset.singleton first)
              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  File "value_segments_bad_successor.proof", line 13, columns 13-91:
  13 |           && edges = Finset.union (Finset.singleton (Edge (first, value, next))) tail_edges
                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

Its footprint must contain the owned node.

  $ caravan --shh value_segments_bad_footprint.ml
  [Error] File "value_segments_bad_footprint.proof", line 22, column 7 to line 23, column 51:
  22 |   fold segment first limit [value] Finset.empty
              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  File "value_segments_bad_footprint.proof", line 12, columns 13-69:
  12 |           && cells = Finset.union (Finset.singleton first) tail_cells
                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
