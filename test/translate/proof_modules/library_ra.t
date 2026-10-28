Library resource algebras expose their declared operations and representation types.

  $ caravan --shh library_ra.ml
  Verification successful.
  $ caravan --shh --emit-rav library_ra.ml > library_ra.rav
  $ raven --shh library_ra.rav
  Verification successful.

Functor arguments must satisfy the Raven library signature.

  $ cp library_ra.ml library_ra_invalid_argument.ml
  $ caravan --shh library_ra_invalid_argument.ml > library_ra_invalid_argument.out 2>&1; status=$?; test "$status" -eq 1 && grep -F 'Type Error:' library_ra_invalid_argument.out
  Type Error: Parameter M requires a module.

Constructor values retain their declared element type.

  $ cp library_ra.ml library_ra_wrong_value.ml
  $ caravan --shh library_ra_wrong_value.ml > library_ra_wrong_value.out 2>&1; status=$?; test "$status" -eq 1 && grep -F 'Type Error:' library_ra_wrong_value.out
  Type Error: This expression should not be a boolean literal, the expected type is

Only declared library members resolve through a module application.

  $ cp library_ra.ml library_ra_unknown_member.ml
  $ caravan --shh library_ra_unknown_member.ml > library_ra_unknown_member.out 2>&1; status=$?; test "$status" -eq 1 && grep -F 'Type Error:' library_ra_unknown_member.out
  Type Error: Unknown proof module member Exclusive.missing.

A module with a carrier type alone is not a resource algebra.

  $ cp library_ra.ml library_ra_non_ra.ml
  $ ! caravan --shh library_ra_non_ra.ml > non_ra.out 2>&1
  $ grep -F 'Type Error: The proof module argument does not implement Library.ResourceAlgebra.' non_ra.out
  Type Error: The proof module argument does not implement Library.ResourceAlgebra.

Library lookup rejects unknown functors after parsing.

  $ cp library_ra.ml library_ra_unknown_functor.ml
  $ ! caravan --shh library_ra_unknown_functor.ml > unknown_functor.out 2>&1
  $ grep -F 'Type Error: Unknown Raven library module NoSuchFunctor.' unknown_functor.out
  Type Error: Unknown Raven library module NoSuchFunctor.

A source module binding shadows an unqualified library functor.

  $ cp library_ra.ml library_ra_shadowed.ml
  $ ! caravan --shh library_ra_shadowed.ml > shadowed.out 2>&1
  $ grep -F 'Type Error: The proof module Auth is not a functor.' shadowed.out
  Type Error: The proof module Auth is not a functor.
