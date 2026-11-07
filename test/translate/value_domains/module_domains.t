Abstract module arguments carry source-value constraints through one shared worker.
Nested lists, options and tuples share domains across generic and concrete callers.

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

Imported container contracts share their dictionaries through checked module views.

  $ caravan --shh container_operation.ml
  Verification successful.
  $ caravan --shh --emit-rav container_operation.ml > container_operation.rav
  $ raven --shh container_operation.rav
  Verification successful.
  $ grep -c '^module Generic_' container_operation.rav
  1
