Raw relaxed fields use the existing journals over options. A cleared word has no
ordinary source validity; aliases retain the same obligation. The generic
validation protocol checks a later atomic head observation before using a payload.

  $ caravan --shh basic.ml
  Verification successful.
  $ caravan --shh validation.ml
  Verification successful.
  $ caravan --shh --emit-rav validation.ml > validation.rav
  $ raven --shh validation.rav
  Verification successful.
  $ caravan --shh shadowed_cast.ml
  Verification successful.
  $ caravan --shh modules.ml
  Verification successful.
  $ caravan --shh -I imports imports.ml
  Verification successful.

Unchecked consumers fail even for booleans, which have no integer range predicate.
Calls, captures, aliases, aggregates and patterns cannot launder speculative values.

  $ caravan --shh unsafe.ml > unsafe.out 2>&1
  [1]
  $ grep -c '^Verification Error: This speculative value may be cleared' unsafe.out
  9
  $ grep -qi 'timeout' unsafe.out
  [1]
  $ caravan --shh spec_unsafe.ml > spec.out 2>&1
  [1]
  $ grep -q 'Use Ghost.raw to refer to a speculative payload' spec.out

Ignoring the validation result cannot justify returning the payload.

  $ sed 's/if Atomic.get head then None else Some value/if Atomic.get head then Some value else Some value/' validation.ml > unchecked.ml
  $ cp validation.proof unchecked.proof
  $ caravan --shh unchecked.ml > unchecked.out 2>&1
  [1]
  $ grep -q 'This speculative value may be cleared' unchecked.out
  $ grep -qi 'timeout' unchecked.out
  [1]

The proof needs the invariant connecting retirement to a head that cannot return.

  $ cp validation.ml aba.ml
  $ sed 's/(Set.mem true phases -> moved)/true/' validation.proof > aba.proof
  $ caravan --shh aba.ml > aba.out 2>&1
  [1]
  $ grep -q 'Verification Error:' aba.out
  $ grep -qi 'timeout' aba.out
  [1]

Clearing before retirement does not preserve the invariant.

  $ sed 's/Atomic.set head true/Atomic.set head false/g' validation.ml > early.ml
  $ sed 's/at (Atomic.set head true)/at (Atomic.set head false)/g' validation.proof > early.proof
  $ caravan --shh early.ml > early.out 2>&1
  [1]
  $ grep -q 'Verification Error:' early.out
  $ grep -qi 'timeout' early.out
  [1]

The unit cast is a cleared-word marker, not a way to obtain an ordinary boolean.
Other casts remain unsupported.

  $ caravan --shh ordinary_cast.ml > ordinary.out 2>&1
  [1]
  $ grep -q 'This speculative value may be cleared' ordinary.out
  $ caravan --shh arbitrary_cast.ml > arbitrary.out 2>&1
  [1]
  $ grep -q 'Unsupported Error:' arbitrary.out

Raw storage must remain explicit across module signatures.

  $ caravan --shh mode_mismatch.ml > mismatch.out 2>&1
  [1]
  $ grep -q 'actual field uses relaxed raw access' mismatch.out
  $ caravan --shh raw_without_relaxed.ml > missing.out 2>&1
  [1]
  $ grep -q 'requires \[@caravan.relaxed\]' missing.out
  $ caravan --shh duplicate_raw.ml > duplicate.out 2>&1
  [1]
  $ grep -q 'Duplicate \[@caravan.raw\]' duplicate.out
  $ caravan --shh raw_on_type.ml > type.out 2>&1
  [1]
  $ grep -q 'belongs on a record field' type.out
