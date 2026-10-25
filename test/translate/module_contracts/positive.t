  $ caravan --shh ordinary.ml
  Verification successful.

  $ caravan --shh atomic.ml
  Verification successful.

  $ caravan --shh local.ml
  Verification successful.

  $ caravan --shh --emit-rav atomic.ml > emitted.rav
  $ raven --shh --typeonly emitted.rav
  Verification successful.

  $ caravan --shh inline.ml
  Verification successful.

  $ caravan --shh checked_again.ml
  Verification successful.

  $ caravan --shh nested.ml
  Verification successful.

  $ caravan --shh manual.ml
  Verification successful.

  $ caravan --shh original_resource.ml
  Verification successful.

  $ caravan --shh local_record.ml
  Verification successful.

  $ caravan --shh persistent.ml
  Verification successful.

  $ caravan --shh inferred_pure.ml
  Verification successful.

  $ caravan --shh implicit_opaque.ml
  Verification successful.

  $ caravan --shh opaque_collection.ml
  Verification successful.

  $ caravan --shh same_actual.ml
  Verification successful.
