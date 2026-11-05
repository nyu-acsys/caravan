The bundled mathematical model and its algebra are checked independently.

  $ caravan --shh --check-stdlib
  Verification successful.
  $ caravan --shh --check-stdlib --emit-rav > list.rav
  $ raven --shh --fingerprints list.rav > list.fingerprints
  $ grep -c 'reverse_involution' list.fingerprints
  1
  $ grep -c 'caravan_stdlib_list_' list.fingerprints
  5

Clients use the checked algebra without checking the library's proofs again.
The mathematical model also applies outside OCaml's machine-integer domain.

  $ caravan --shh client.ml
  Verification successful.
  $ caravan --shh --emit-rav client.ml > client.rav
  $ raven --shh --fingerprints client.rav > client.fingerprints
  $ ! grep -q 'caravan_stdlib_list_' client.fingerprints

A source filename cannot make an ordinary user proof a trusted library proof.

  $ mkdir -p caravan/stdlib
  $ cp path_collision.ml caravan/stdlib/list.ml
  $ cp path_collision.proof caravan/stdlib/list.proof
  $ caravan --shh caravan/stdlib/list.ml > collision.out 2>&1
  [1]
  $ grep -c 'A postcondition may not hold' collision.out
  2
  $ ! grep -qi 'timed out' collision.out
  $ caravan --shh --emit-rav caravan/stdlib/list.ml > collision.rav
  $ raven --shh --fingerprints collision.rav > collision.fingerprints 2> collision-native.out
  [1]
  $ grep -c 'forged_' collision.fingerprints
  2
