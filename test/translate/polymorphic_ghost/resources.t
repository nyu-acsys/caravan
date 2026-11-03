Resource families infer the same type index through constructors, constants, aliases, and Auth, including ghost allocation and updates.

  $ caravan --shh resources.ml
  Verification successful.
  $ caravan --shh --emit-rav resources.ml > resources.rav
  $ raven --shh resources.rav
  Verification successful.

Different nonzero family arities require an explicit reindexing rather than an implicit product.

  $ caravan --shh resource_arity_fail.ml > resource_arity_fail.out 2>&1
  [1]
  $ grep -q 'equal nonzero argument arities' resource_arity_fail.out
  $ ! grep -q 'Internal Error:' resource_arity_fail.out
