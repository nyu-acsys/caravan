A generic worker keeps the input algebra symbolic in predicate types and contracts.

  $ caravan --shh ra_exports_input_contract.ml
  Verification successful.
  $ caravan --shh --emit-rav ra_exports_input_contract.ml > ra_exports_input_contract.rav
  $ raven --shh ra_exports_input_contract.rav
  Verification successful.
  $ grep -c '^module Generic_' ra_exports_input_contract.rav
  1
  $ grep -c '^module Applied' ra_exports_input_contract.rav
  2
