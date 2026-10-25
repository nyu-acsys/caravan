  $ caravan --shh ordinary.ml
  Verification successful.

  $ caravan --shh atomic.ml
  Verification successful.

  $ caravan --shh nested.ml
  Verification successful.

  $ caravan --shh functor_alias.ml
  Verification successful.

  $ caravan --shh --emit-rav atomic.ml > emitted.rav
  $ raven --shh --typeonly emitted.rav
  Verification successful.

  $ caravan --shh captured.ml
  Verification successful.

  $ caravan --shh manual.ml
  Verification successful.

  $ caravan --shh pure_helper.ml
  Verification successful.

  $ caravan --shh result_alias.ml
  Verification successful.

  $ caravan --shh nested_application.ml
  Verification successful.

  $ caravan --shh inline_parameter.ml
  Verification successful.

  $ caravan --shh fresh_variant.ml
  Verification successful.

  $ caravan --shh fresh_record.ml
  Verification successful.

  $ caravan --shh unit.ml
  Verification successful.
