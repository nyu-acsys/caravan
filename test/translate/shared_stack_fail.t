  $ caravan --shh shared_stack_fail.ml
  [Error] File "shared_stack_fail.ml", line 6, columns 33-33:
  6 | let create () = Atomic.make [ 1 ]
                                       ^
  Verification Error: The invariant is_stack may not hold when this function returns.
  File "shared_stack_fail.proof", line 4, columns 10-18:
  4 | invariant is_stack (t : t) (s : state) = own t s.items
                ^^^^^^^^
  Related Location: The invariant.
  [Error] File "shared_stack_fail.ml", line 11, columns 49-49:
  11 |   if not (Atomic.compare_and_set t before before) then push t value
                                                        ^
  Verification Error: The invariant is_stack may not hold after this step.
  File "shared_stack_fail.proof", line 4, columns 10-18:
  4 | invariant is_stack (t : t) (s : state) = own t s.items
                ^^^^^^^^
  Related Location: The invariant.
  [Error] File "shared_stack_fail.ml", line 14, columns 29-29:
  14 | let clear t = Atomic.set t []
                                    ^
  Verification Error: The invariant is_stack may not hold after this step.
  File "shared_stack_fail.proof", line 4, columns 10-18:
  4 | invariant is_stack (t : t) (s : state) = own t s.items
                ^^^^^^^^
  Related Location: The invariant.
  [1]
