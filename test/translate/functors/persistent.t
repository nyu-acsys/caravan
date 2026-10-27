Invariant parameters remain explicit, including trailing integer parameters.

  $ caravan --shh generic_persistent_versioned.ml
  Verification successful.

  $ caravan --shh --emit-rav generic_persistent_versioned.ml > versioned.rav
  $ raven --shh --fingerprints versioned.rav > versioned.fingerprints
  $ grep -c ' Generic_.*\.method_' versioned.fingerprints
  1
  $ raven --shh versioned.rav
  Verification successful.

  $ sed 's/Repeated.touch x 42/Repeated.touch x 41/' generic_persistent_versioned.ml > wrong_version.ml
  $ caravan --shh wrong_version.ml
  [Error] File "wrong_version.ml", line 19, columns 2-21:
  19 |   Repeated.touch x 41
         ^^^^^^^^^^^^^^^^^^^
  Verification Error: Cannot call method_touch. The invariant versioned required by method_touch is not available in the current mask.
  [1]

Native result layouts also retain invariant identities across repeated applications.

  $ caravan --shh generic_persistent_layout.ml
  Verification successful.

  $ caravan --shh --emit-rav generic_persistent_layout.ml > layout.rav
  $ raven --shh --fingerprints layout.rav > layout.fingerprints
  $ grep -c ' World_.*\.method_' layout.fingerprints
  2
  $ grep -c '^module Layout.*Fresh()' layout.rav
  2
  $ raven --shh layout.rav
  Verification successful.

A different invariant on the same source type cannot supply a worker's mask.

  $ caravan --shh generic_persistent_fail.ml
  [Error] File "generic_persistent_fail.ml", line 17, columns 15-31:
  17 | let client x = Repeated.touch x
                      ^^^^^^^^^^^^^^^^
  Verification Error: Cannot call method_touch. The invariant shared required by method_touch is not available in the current mask.
  [1]

Manual proof scopes continue to use verified specializations.

  $ caravan --shh --emit-rav manual.ml > manual.rav
  $ sed -n '/^module Generic_.*\[/p' manual.rav
  $ raven --shh manual.rav
  Verification successful.
