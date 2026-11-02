Generic logical functions and lemmas share bodies under static modules, source
functors, aliases, and repeated applications while retaining captured parameter types.

  $ caravan --shh modules.ml
  Verification successful.
  $ caravan --shh --emit-rav modules.ml > modules.rav
  $ grep -c 'Generic_.*\[Parameter:' modules.rav
  1
  $ grep -c 'lemma make_preserve(' modules.rav
  1
  $ grep -c 'lemma make_keep(' modules.rav
  1
  $ raven --shh modules.rav
  Verification successful.
