Function value aliases and alias chains reuse the defining polymorphic worker.

  $ caravan --shh aliases.ml
  Verification successful.
  $ caravan --shh --emit-rav aliases.ml > aliases.rav
  $ grep -c '^module Poly_id.*\[' aliases.rav
  1
  $ raven --shh aliases.rav
  Verification successful.

A value alias cannot add a separate proof contract.

  $ caravan --shh alias_contract.ml > alias_contract.out 2>&1
  [1]
  $ grep -q 'Contracts on function value aliases' alias_contract.out
  $ ! grep -q 'Internal Error:' alias_contract.out
