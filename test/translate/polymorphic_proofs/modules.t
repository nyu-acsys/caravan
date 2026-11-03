Generic predicates, logical functions and lemmas share bodies under static modules,
named and unit functors, aliases and repeated applications while retaining captured types.

  $ caravan --shh modules.ml
  Verification successful.
  $ caravan --shh --emit-rav modules.ml > modules.rav
  $ grep -c 'Generic_.*\[Parameter:' modules.rav
  2
  $ grep -c 'lemma make_preserve(' modules.rav
  1
  $ grep -c 'lemma make_keep(' modules.rav
  1
  $ grep -c 'lemma factory_keep_cell(' modules.rav
  1
  $ raven --shh modules.rav
  Verification successful.

Module-qualified predicates retain the relation between their location and payload types.

  $ mkdir bad_cells
  $ cp modules.ml bad_cells/
  $ sed 's/ensures (cell location value)/ensures (cell location true)/' modules.proof > bad_cells/modules.proof
  $ caravan --shh bad_cells/modules.ml > bad_cells.out 2>&1
  [1]
  $ grep -Eq 'Type Error:|Unsupported Error: This polymorphic function occurrence or signature alias is not supported yet' bad_cells.out
  $ ! grep -Eq 'Syntax Error:|Internal Error:' bad_cells.out
