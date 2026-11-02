Generic logical functions and lemmas share one body across inferred type arguments,
including contextual result types and omitted implicit lemma arguments.
Lemma return bindings also determine type parameters used only by returned values.
Annotated proof let bindings provide the same context before result inference.

  $ caravan --shh basic.ml
  Verification successful.
  $ caravan --shh --emit-rav basic.ml > basic.rav
  $ grep -c 'func identity(' basic.rav
  1
  $ raven --shh basic.rav
  Verification successful.
