Action mismatches, forbidden invariant updates, and incorrect read linearizations
are rejected on a two-state counter. Its constructor and declared transition are
valid controls. Diagnostics are checked without normalizing solver timeouts.

  $ caravan --shh action_steps_fail.ml
  [Error] File "action_steps_fail.ml", line 9, columns 28-56:
  9 | let rec wrong_action c = if Atomic.compare_and_set c 0 0 then () else wrong_action c
                                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This step may not perform the action wrong_action.
  [Error] File "action_steps_fail.ml", line 12, columns 28-56:
  12 | let forbidden_update c = if Atomic.compare_and_set c 0 2 then () else ()
                                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This step may change the state of is_counter in a way that no action allows; if it performs one, say so, as (*@ performs a *).
  File "action_steps_fail.proof", line 3, columns 10-20:
  3 | invariant is_counter (c : t) (s : state) =
                ^^^^^^^^^^
  Related Location: The invariant.
  [Error] File "action_steps_fail.ml", line 15, columns 21-33:
  15 | let wrong_result c = Atomic.get c (*@ commit *)
                            ^^^^^^^^^^^^
  Verification Error: The atomic postcondition may not hold after this step, which linearizes the function.
  File "action_steps_fail.mli", line 29, columns 19-39:
  29 |     atomic ensures counter c n && r = 2 *)
                          ^^^^^^^^^^^^^^^^^^^^
  Related Location: The atomic postcondition.
  [Error] File "action_steps_fail.ml", line 15, columns 21-33:
  15 | let wrong_result c = Atomic.get c (*@ commit *)
                            ^^^^^^^^^^^^
  Verification Error: A postcondition may not hold at this return point.
  File "action_steps_fail.mli", line 29, columns 34-39:
  29 |     atomic ensures counter c n && r = 2 *)
                                         ^^^^^
  Related Location: This assertion may not hold.
  [1]
