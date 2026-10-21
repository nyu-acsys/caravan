A contract reads the heap only through own, and a free name needs a type; each file
has its own run.

  $ caravan --shh heap_error_1.ml
  [Error] File "heap_error_1.ml", line 5, columns 13-20:
  5 |     requires c.count > 0 *)
                   ^^^^^^^
  Type Error: A contract reads c.count through own, as in own c.count v.
  [1]
  $ caravan --shh heap_error_2.ml
  [Error] File "heap_error_2.ml", line 3, columns 13-18:
  3 |     requires x < n *)
                   ^^^^^
  Type Error: Unbound name n.
  [1]
