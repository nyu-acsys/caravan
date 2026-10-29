Unit functor proof declarations resolve under a containing module and remain distinct across fresh applications.

  $ caravan --shh uniform_unit.ml
  Verification successful.
  $ caravan --shh --emit-rav uniform_unit.ml > uniform_unit.rav
  $ raven --shh uniform_unit.rav
  Verification successful.

The model type of one fresh unit application cannot be passed to another.

  $ cp uniform_unit.ml uniform_unit_wrong_model.ml
  $ ! caravan --shh uniform_unit_wrong_model.ml > uniform_unit_wrong_model.out 2>&1
  $ grep -q 'Type Error:' uniform_unit_wrong_model.out
  $ ! grep -q 'Internal Error:' uniform_unit_wrong_model.out

The ghost field and private predicate of a fresh unit application are separate resources.

  $ cp uniform_unit.ml uniform_unit_wrong_ghost.ml
  $ ! caravan --shh uniform_unit_wrong_ghost.ml > uniform_unit_wrong_ghost.out 2>&1
  $ grep -Eq 'Verification Error:|Type Error:' uniform_unit_wrong_ghost.out
  $ ! grep -q 'Internal Error:' uniform_unit_wrong_ghost.out

Each fresh unit application has its own AU facade token, while an alias shares its token.

  $ caravan --shh uniform_unit_au.ml
  Verification successful.
  $ caravan --shh --emit-rav uniform_unit_au.ml > uniform_unit_au.rav
  $ raven --shh uniform_unit_au.rav
  Verification successful.
  $ cp uniform_unit_au.ml uniform_unit_au_wrong_token.ml
  $ ! caravan --shh uniform_unit_au_wrong_token.ml > uniform_unit_au_wrong_token.out 2>&1
  $ grep -q 'Type Error:' uniform_unit_au_wrong_token.out
  $ ! grep -q 'Internal Error:' uniform_unit_au_wrong_token.out

A unit functor verifies one counter worker for fresh applications and keeps its invariant separate.

  $ caravan --shh uniform_unit_state.ml
  Verification successful.
  $ caravan --shh --emit-rav uniform_unit_state.ml > uniform_unit_state.rav
  $ raven --shh uniform_unit_state.rav
  Verification successful.
  $ ! caravan --shh uniform_unit_state_interchange_fail.ml > uniform_unit_state_interchange_fail.out 2>&1
  $ grep -q 'Verification Error: Cannot call method_set_one. The invariant' uniform_unit_state_interchange_fail.out
  $ ! grep -q 'Internal Error:' uniform_unit_state_interchange_fail.out

A curried named functor preserves both argument contracts through direct and partial applications.

  $ caravan --shh uniform_curried.ml
  Verification successful.
  $ caravan --shh --emit-rav uniform_curried.ml > uniform_curried.rav
  $ raven --shh uniform_curried.rav
  Verification successful.
  $ grep -c 'Generic_.*\[Parameter_0:' uniform_curried.rav
  1

Unit and named parameters can appear in either order.

  $ caravan --shh uniform_mixed.ml
  Verification successful.
  $ caravan --shh --emit-rav uniform_mixed.ml > uniform_mixed.rav
  $ raven --shh uniform_mixed.rav
  Verification successful.

Fresh unit stages remain distinct after further applicative stages.

  $ cp uniform_mixed.ml uniform_mixed_fresh_fail.ml
  $ ! caravan --shh uniform_mixed_fresh_fail.ml > uniform_mixed_fresh_fail.out 2>&1
  $ grep -q 'Type Error:' uniform_mixed_fresh_fail.out
  $ ! grep -q 'Internal Error:' uniform_mixed_fresh_fail.out

An ascription on a completed curried application hides its proof model.

  $ cat uniform_curried.ml > uniform_curried_hidden.ml
  $ ! caravan --shh uniform_curried_hidden.ml > uniform_curried_hidden.out 2>&1
  $ grep -q 'Unbound type constructor Hidden.choice' uniform_curried_hidden.out
  $ ! grep -q 'Internal Error:' uniform_curried_hidden.out
