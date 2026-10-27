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

  $ caravan --shh --emit-rav checked_again.ml > checked_again.rav
  $ raven --shh --fingerprints checked_again.rav > checked_again.fingerprints
  $ sed -n 's/^[0-9a-f]\{32\} //p' checked_again.fingerprints
  client
  Checked_original.checked_original_touch
  Checked_original.checked_original_read

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

  $ caravan --shh repeated_pure.ml
  Verification successful.

  $ caravan --shh --emit-rav repeated_pure.ml > repeated_pure.rav
  $ grep -c '^proc published_' repeated_pure.rav
  1
  $ raven --shh --typeonly repeated_pure.rav
  Verification successful.

  $ caravan --shh implicit_opaque.ml
  Verification successful.

  $ caravan --shh opaque_collection.ml
  Verification successful.

  $ caravan --shh same_actual.ml
  Verification successful.

  $ caravan --shh repeated_atomic.ml
  Verification successful.

  $ caravan --shh --emit-rav repeated_atomic.ml > repeated_atomic.rav
  $ raven --shh --fingerprints repeated_atomic.rav > repeated_atomic.fingerprints
  $ sed -n 's/^[0-9a-f]\{32\} //p' repeated_atomic.fingerprints
  client
  Checked_original.checked_original_touch
  Checked_original.checked_original_read
