Explicitly pure imported functions share one contract between runtime and logical
calls, including aliases, polymorphic instances and guarded preconditions.

  $ caravan --shh client.ml
  Verification successful.

  $ caravan --shh --emit-rav client.ml > emitted.rav
  $ raven --shh --typeonly emitted.rav
  Verification successful.

Incorrect results and logical calls outside their contract domains are rejected.

  $ caravan --shh wrong_result.ml
  [Error] File "wrong_result.ml", line 1, columns 54-54:
  1 | let wrong (value : bool) = Pure_library.identity value
                                                            ^
  Verification Error: A postcondition may not hold at this return point.
  File "wrong_result.ml", line 2, columns 33-49:
  2 | (*@ result = wrong value ensures result =/= value *)
                                       ^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh outside_precondition.ml
  [Error] File "outside_precondition.ml", line 1, columns 17-17:
  1 | let wrong () = ()
                       ^
  Verification Error: A postcondition may not hold at this return point.
  File "outside_precondition.ml", line 2, columns 21-51:
  2 | (*@ wrong () ensures Pure_library.bounded (-1) >= 0 *)
                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh outside_domain.ml
  [Error] File "outside_domain.ml", line 1, columns 17-17:
  1 | let wrong () = ()
                       ^
  Verification Error: A postcondition may not hold at this return point.
  File "outside_domain.ml", line 2, columns 21-67:
  2 | (*@ wrong () ensures Pure_library.identity (max_int + 1) <= max_int *)
                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh -I heap_library heap_client.ml
  [Error] File "heap_library/heap.mli", line 1, columns 0-25:
  1 | val read : int ref -> int
      ^^^^^^^^^^^^^^^^^^^^^^^^^
  Unsupported Error: A pure library function whose contract depends on heap resources is not supported yet.
  [1]

Runtime calls must establish their preconditions.

  $ caravan --shh runtime_precondition.ml
  [Error] File "runtime_precondition.ml", line 1, columns 15-40:
  1 | let wrong () = Pure_library.bounded (-1)
                     ^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: A precondition may not hold for this call.
  File "./pure_library.mli", line 11, columns 13-23:
  11 |     requires value >= 0
                    ^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
