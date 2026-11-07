Automatic state fields are allocated on a datatype-valued atomic's layout field.

  $ caravan --shh generic_variant_cell.ml
  Verification successful.
  $ caravan --shh --emit-rav generic_variant_cell.ml > emitted.rav
  $ raven --shh emitted.rav
  Verification successful.
