Raw relaxed fields use the existing journals over options. A cleared word has no
ordinary source validity; aliases retain the same obligation. The generic
validation protocol checks a later atomic head observation before using a payload.

  $ caravan --shh basic.ml
  Verification successful.
  $ caravan --shh validation.ml
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
