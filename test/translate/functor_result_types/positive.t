  $ caravan --shh variant.ml
  Verification successful.

  $ caravan --shh recursive.ml
  Verification successful.

  $ caravan --shh record.ml
  Verification successful.

  $ caravan --shh mutable_record.ml
  Verification successful.

  $ caravan --shh distinct.ml
  Verification successful.

  $ caravan --shh sealed.ml
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

  $ caravan --shh --emit-rav distinct.ml > distinct.rav
  $ raven --shh --typeonly distinct.rav
  Verification successful.

  $ caravan --shh --emit-rav sealed.ml > sealed.rav
  $ raven --shh --typeonly sealed.rav
  Verification successful.

  $ grep -c '^[[:space:]]*field .*_value[^:]*:' mutable_record.rav
  1

  $ grep -c '^[[:space:]]*field .*_contents[^:]*:' distinct.rav
  1

  $ grep -c '^module Layout.*Fresh()' distinct.rav
  2

  $ grep -c '^[[:space:]]*field .*_contents[^:]*:' sealed.rav
  1

  $ caravan --shh nested.ml
  Verification successful.

  $ caravan --shh --emit-rav nested.ml > nested.rav
  $ raven --shh --typeonly nested.rav
  Verification successful.

  $ caravan --shh application_paths.ml
  Verification successful.

  $ caravan --shh payload.ml
  Verification successful.

  $ caravan --shh sealed_nested.ml
  Verification successful.

  $ caravan --shh --emit-rav sealed_nested.ml > sealed_nested.rav
  $ raven --shh --typeonly sealed_nested.rav
  Verification successful.

  $ grep -c '^[[:space:]]*field .*_contents[^:]*:' sealed_nested.rav
  1
  $ caravan --shh polymorphic.ml
  Verification successful.
