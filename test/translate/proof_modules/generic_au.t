A named generic functor verifies one AU worker and exposes application-specific facades.

  $ caravan --shh generic_au.ml
  Verification successful.
  $ caravan --shh --emit-rav generic_au.ml > generic_au.rav
  $ raven --shh generic_au.rav
  Verification successful.
  $ grep -c '^module Generic_' generic_au.rav
  1
  $ grep -c '^  lemma .*preserve_private' generic_au.rav
  1

Different applications have distinct AU token types.

  $ ! caravan --shh generic_au_wrong_token.ml > generic_au_wrong_token.out 2>&1
  $ grep -q 'Type Error:' generic_au_wrong_token.out
  $ ! grep -q 'Internal' generic_au_wrong_token.out

An AU token can only be bound in its operation, including generic workers.

  $ ! caravan --shh generic_au_wrong_bind.ml > generic_au_wrong_bind.out 2>&1
  $ grep -F 'Type Error: An AU token can only be bound in its own procedure.' generic_au_wrong_bind.out
  Type Error: An AU token can only be bound in its own procedure.

The generic worker still enforces the AU lifecycle.

  $ ! caravan --shh generic_au_double_open.ml > generic_au_double_open.out 2>&1
  $ grep -q 'Verification Error: Atomic token .* is already open.' generic_au_double_open.out

A sealed functor verifies its private AU proof and hides the facade from callers.

  $ cp generic_au_sealed.ml generic_au_sealed_ok.ml
  $ caravan --shh generic_au_sealed_ok.ml
  Verification successful.
  $ caravan --shh --emit-rav generic_au_sealed_ok.ml > generic_au_sealed_ok.rav
  $ raven --shh generic_au_sealed_ok.rav
  Verification successful.

  $ ! caravan --shh generic_au_sealed.ml > generic_au_sealed.out 2>&1
  $ grep -q 'Type Error:' generic_au_sealed.out
  $ ! grep -q 'Internal' generic_au_sealed.out

Checked argument operations are not treated as the functor's own implementation.

  $ cp generic_au.ml generic_au_checked.ml
  $ ! caravan --shh generic_au_checked.ml > generic_au_checked.out 2>&1
  $ grep -F 'Type Error: An AU facade must name a procedure in this implementation.' generic_au_checked.out
  Type Error: An AU facade must name a procedure in this implementation.
