A result slot can be cleared after retirement. A speculative read becomes an
ordinary value only after the atomic retirement check validates it.

  $ caravan --shh raw_result.ml
  Verification successful.

Returning the speculative payload on the retired branch fails verification.

  $ sed 's/if Atomic.get head then None else Some value/if Atomic.get head then Some value else Some value/' raw_result.ml > unchecked.ml
  $ cp raw_result.proof unchecked.proof
  $ caravan --shh unchecked.ml > unchecked.out 2>&1
  [1]
  $ grep -q 'This speculative value may be cleared' unchecked.out
  $ grep -qi 'timeout' unchecked.out
  [1]
