Raven checks invariant closure, access permissions, restoration, and the public
contract for manual proofs.

  $ caravan --shh manual_access_fail.ml
  [Error] File "manual_access_fail.ml", line 1, columns 51-52:
  1 | let unclosed (cell : int Atomic.t) = Atomic.get cell
                                                         ^
  Verification Error: Missing fold for unfolded invariant zero(cell).
  File "manual_access_fail.ml", line 3, columns 11-20:
  3 |     unfold zero cell;
                 ^^^^^^^^^
  Related Location: zero(cell) was unfolded here.
  [1]

  $ caravan --shh manual_permissions_fail.ml
  [Error] File "manual_permissions_fail.ml", line 1, columns 36-51:
  1 | let unowned (cell : int Atomic.t) = Atomic.get cell
                                          ^^^^^^^^^^^^^^^
  Verification Error: Could not assert sufficient permissions to access this field.
  [Error] File "manual_permissions_fail.ml", line 1, columns 51-51:
  1 | let unowned (cell : int Atomic.t) = Atomic.get cell
                                                         ^
  Verification Error: A postcondition may not hold at this return point.
  File "manual_permissions_fail.ml", line 1, columns 0-51:
  1 | let unowned (cell : int Atomic.t) = Atomic.get cell
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

  $ caravan --shh manual_restoration_fail.ml
  [Error] File "manual_restoration_fail.ml", line 5, columns 9-18:
  5 |     fold zero cell;
               ^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  File "manual_restoration_fail.ml", line 5, columns 9-18:
  5 |     fold zero cell;
               ^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]

  $ caravan --shh manual_contract_fail.ml
  [Error] File "manual_contract_fail.ml", line 1, columns 55-55:
  1 | let false_claim (cell : int Atomic.t) = Atomic.get cell
                                                             ^
  Verification Error: A postcondition may not hold at this return point.
  File "manual_contract_fail.ml", line 9, columns 70-80:
  9 | (*@ result = false_claim cell requires zero cell ensures zero cell && result = 1 *)
                                                                            ^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
