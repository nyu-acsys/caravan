Atomic contracts the translation cannot meet; each file has its own run.

  $ caravan --shh atomic_contract_error_1.ml
  [Error] File "atomic_contract_error_1.ml", line 5, columns 0-24:
  5 | let release (l : t) = ()
      ^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: This function may return before it linearizes: no step commits its atomic contract.
  [1]
  $ caravan --shh atomic_contract_error_2.ml
  [Error] File "atomic_contract_error_2.ml", line 6, columns 14-18:
  6 | (*@ returning true -> commit *)
                    ^^^^
  Type Error: Only a read can linearize by its value.
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
  $ caravan --shh atomic_contract_error_5.ml
  [Error] File "atomic_contract_error_5.ml", line 7, columns 0-13:
  7 | (*@ commit *)
      ^^^^^^^^^^^^^
  Type Error: This annotation does not follow an atomic step, as Atomic.get t.
  [1]
  $ caravan --shh atomic_contract_error_6.ml
  [Error] File "atomic_contract_error_6.ml", line 6, columns 35-39:
  6 |   match Atomic.get t (*@ returning rest -> commit *) with
                                         ^^^^
  Unsupported Error: A pattern other than a constructor, after returning, is not supported yet.
  [1]
  $ caravan --shh atomic_contract_error_7.ml
  [Error] File "atomic_contract_error_7.ml", line 6, column 0 to line 10, column 73:
  6 | let rec pop_opt (t : t) =
      ^^^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: This function may return before it linearizes, on some path: annotate the step that linearizes it there, as (*@ commit *) or (*@ returning [] -> commit *).
  [1]
