  $ caravan --shh variant.ml
  Verification successful.

  $ caravan --shh record.ml
  Verification successful.

  $ caravan --shh mutable_record.ml
  Verification successful.

  $ caravan --shh manifest_alias.ml
  Verification successful.

  $ caravan --shh captured.ml
  Verification successful.

  $ caravan --shh nested.ml
  Verification successful.

  $ caravan --shh named_argument.ml
  Verification successful.

  $ caravan --shh named_legal.ml
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
  2

  $ caravan --shh --emit-rav manifest_alias.ml > manifest_alias.rav
  $ raven --shh --typeonly manifest_alias.rav
  Verification successful.

  $ caravan --shh --emit-rav captured.ml > captured.rav
  $ raven --shh --typeonly captured.rav
  Verification successful.

  $ caravan --shh --emit-rav nested.ml > nested.rav
  $ raven --shh --typeonly nested.rav
  Verification successful.

  $ grep -c '^[[:space:]]*field .*_contents[^:]*:' nested.rav
  2

  $ caravan --shh --emit-rav named_argument.ml > named_argument.rav
  $ raven --shh --typeonly named_argument.rav
  Verification successful.

  $ grep -c '^[[:space:]]*field .*_contents[^:]*:' named_argument.rav
  2

  $ caravan --shh --emit-rav named_legal.ml > named_legal.rav
  $ raven --shh --typeonly named_legal.rav
  Verification successful.

  $ caravan --shh manual.ml
  Verification successful.

  $ caravan --shh ascribed.ml
  Verification successful.

  $ caravan --shh --emit-rav ascribed.ml > ascribed.rav
  $ raven --shh --typeonly ascribed.rav
  Verification successful.
