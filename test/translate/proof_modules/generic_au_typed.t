An imported abstract argument type remains tied to each AU application.

  $ caravan --shh -I generic_au_lib generic_au_typed.ml
  Verification successful.
  $ caravan --shh -I generic_au_lib --emit-rav generic_au_typed.ml > generic_au_typed.rav
  $ raven --shh generic_au_typed.rav
  Verification successful.
  $ grep -c '^module Generic_' generic_au_typed.rav
  1
  $ grep -c '^  lemma .*preserve_private' generic_au_typed.rav
  1
