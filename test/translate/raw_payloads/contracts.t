Raw helper binders carry cleared words without granting source-level validity.
The same ABI is preserved by contracts, aliases, imports and functors.
Result-position wrappers preserve raw transport through lets, sequences and opens.

  $ caravan --shh contracts.ml
  Verification successful.
  $ caravan --shh --emit-rav contracts.ml > contracts.rav
  $ raven --shh contracts.rav
  Verification successful.
  $ caravan --shh -I imports import_contracts.ml
  Verification successful.
  $ caravan --shh contract_modules.ml
  Verification successful.
  $ caravan --shh inherited.ml
  Verification successful.

Ordinary consumers must still validate raw parameters and returned words.

  $ caravan --shh contract_consumers.ml > consumers.out 2>&1
  [1]
  $ grep -c '^Verification Error: This speculative value may be cleared' consumers.out
  2
  $ grep -qi timeout consumers.out
  [1]
  $ caravan --shh contract_errors.ml > patterns.out 2>&1
  [1]
  $ grep -q 'A raw parameter requires a variable pattern' patterns.out

Public aliases cannot erase raw calling conventions.

  $ caravan --shh alias_erasure.ml > alias.out 2>&1
  [1]
  $ grep -q 'Argument 1 has different raw modes' alias.out
  $ caravan --shh result_alias_erasure.ml > result.out 2>&1
  [1]
  $ grep -q 'result has different raw modes' result.out
  $ caravan --shh alias_erasure_root/erase.ml > interface.out 2>&1
  [1]
  $ grep -q 'Argument 1 has different raw modes' interface.out

Ordinary branch results remain usable in proofs in a module with raw storage.

  $ caravan --shh ordinary_branches.ml
  Verification successful.
