Abstract module arguments carry source-value constraints through one shared worker.
List identities preserve the same domain across generic and concrete callers.

  $ caravan --shh module_domains.ml
  Verification successful.
  $ caravan --shh --emit-rav module_domains.ml > module_domains.rav
  $ raven --shh module_domains.rav
  Verification successful.
  $ grep -c '^module Generic_' module_domains.rav
  1

An imported abstract source type has an unknown domain, with no inhabitant promised.

  $ caravan --shh abstract_domain.ml
  Verification successful.
  $ caravan --shh opaque_witness.ml > opaque_witness.out 2>&1
  [1]
  $ grep -q 'Verification Error:' opaque_witness.out
  $ ! grep -q 'Internal Error:' opaque_witness.out

Imported runtime constants guarantee admissibility, unlike raw logical defaults.

  $ caravan --shh constant_domain.ml
  Verification successful.
