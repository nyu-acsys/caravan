Atomic contracts the translation cannot meet; each file has its own run.

  $ caravan --shh atomic_contract_error_1.ml
  [Error] File "atomic_contract_error_1.ml", line 5, columns 0-24:
  5 | let release (l : t) = ()
      ^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: This function may return before it linearizes: no step commits its atomic contract.
  [1]
  $ caravan --shh atomic_contract_error_2.ml
  [Error] File "atomic_contract_error_2.ml", line 5, columns 0-55:
  5 | let try_acquire l = Atomic.compare_and_set l false true
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Unsupported Error: An atomic contract of a function with a result is not supported yet.
  [1]
  $ caravan --shh atomic_contract_error_3.ml
  [Error] File "atomic_contract_error_3.ml", line 6, column 2 to line 8, column 6:
  6 |   while not (Atomic.compare_and_set l false true) do
        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Unsupported Error: A loop in a function with an atomic contract, before it linearizes, is not supported yet.
  [1]
  $ caravan --shh atomic_contract_error_4.ml
  [Error] File "atomic_contract_error_4.ml", line 8, columns 10-45:
  8 |   let _ = Atomic.compare_and_set l false true in
                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: Caravan cannot tell whether the function has linearized before this step.
  [1]
