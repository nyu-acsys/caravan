  $ caravan --shh variant.ml
  Verification successful.

  $ caravan --shh record.ml
  Verification successful.

  $ caravan --shh mutable_record.ml
  Verification successful.

  $ caravan --shh distinct.ml
  Verification successful.

  $ caravan --shh trailing_unit.ml
  Verification successful.

  $ caravan --shh intermediate_unit.ml
  Verification successful.

  $ caravan --shh captured.ml
  Verification successful.

  $ caravan --shh --emit-rav variant.ml > variant.rav
  $ raven --shh --typeonly variant.rav
  Verification successful.

  $ caravan --shh --emit-rav record.ml > record.rav
  $ raven --shh --typeonly record.rav
  Verification successful.

  $ caravan --shh --emit-rav mutable_record.ml > mutable_record.rav
  $ raven --shh --typeonly mutable_record.rav
  Verification successful.

  $ grep -c '^[[:space:]]*field .*_contents[^:]*:' mutable_record.rav
  1

  $ caravan --shh --emit-rav distinct.ml > distinct.rav
  $ raven --shh --typeonly distinct.rav
  Verification successful.

  $ grep -c '^[[:space:]]*field .*_contents[^:]*:' distinct.rav
  2

  $ caravan --shh --emit-rav trailing_unit.ml > trailing_unit.rav
  $ raven --shh --typeonly trailing_unit.rav
  Verification successful.

  $ grep -c '^[[:space:]]*field .*_contents[^:]*:' trailing_unit.rav
  2

  $ caravan --shh --emit-rav intermediate_unit.ml > intermediate_unit.rav
  $ raven --shh --typeonly intermediate_unit.rav
  Verification successful.

  $ caravan --shh --emit-rav captured.ml > captured.rav
  $ raven --shh --typeonly captured.rav
  Verification successful.

  $ caravan --shh dependent.ml
  Verification successful.

  $ caravan --shh -I ../functors dependent_resource.ml
  Verification successful.

  $ caravan --shh inline_unit.ml
  Verification successful.

  $ caravan --shh --emit-rav inline_unit.ml > inline_unit.rav
  $ raven --shh --typeonly inline_unit.rav
  Verification successful.

  $ grep -c '^[[:space:]]*field .*_contents[^:]*:' inline_unit.rav
  2
