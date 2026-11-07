Parameterized proof records retain mathematical payload domains.

  $ caravan --shh mathematical.ml
  Verification successful.
  $ caravan --shh --emit-rav mathematical.ml > mathematical.rav
  $ raven --shh mathematical.rav
  Verification successful.

  $ caravan --shh bad_mathematical.ml > bad_mathematical.out 2>&1
  [1]
  $ grep -q 'Verification Error:' bad_mathematical.out
  $ ! grep -q 'Internal Error:' bad_mathematical.out

  $ caravan --shh bad_contract.ml > bad_contract.out 2>&1
  [1]
  $ grep -q 'Verification Error:' bad_contract.out
  $ ! grep -q 'Internal Error:' bad_contract.out

Pure source calls do not provide bounds for arbitrary mathematical inputs.

  $ caravan --shh bad_runtime.ml > bad_runtime.out 2>&1
  [1]
  $ grep -q 'Verification Error:' bad_runtime.out
  $ ! grep -q 'Internal Error:' bad_runtime.out
