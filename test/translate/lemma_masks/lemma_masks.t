Explicit lemma masks preserve the distinction between inferred footprints, empty
footprints, specific invariant instances and whole invariant namespaces.

  $ caravan --shh masks.ml
  Verification successful.
  $ caravan --shh closed_fail.ml > closed_fail.out 2>&1
  [1]
  $ grep -q 'Verification Error:' closed_fail.out
  $ grep -qi 'timeout' closed_fail.out
  [1]
  $ caravan --shh nonresource_fail.ml > nonresource_fail.out 2>&1
  [1]
  $ grep -qi 'predicate\|invariant' nonresource_fail.out
