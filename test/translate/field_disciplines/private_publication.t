A CAS release can publish the current private-write event before freezing. A
failed CAS retains mutable ownership so a later attempt can publish a rewrite.

  $ caravan --shh private_publication.ml
  Verification successful.

Acquiring a release bound allows an arbitrary recipient to adopt writer
provenance. Possessing the same bound without an acquire does not.

  $ caravan --shh private_adopt_fail.ml > adopt.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' adopt.out
  $ grep -qi 'timeout' adopt.out
  [1]

An unrelated atomic read cannot launder ownership taken from an invariant into
current-writer provenance by overwriting the field.

  $ caravan --shh unordered_handoff_fail.ml > unordered.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' unordered.out
  $ grep -qi 'timeout' unordered.out
  [1]
