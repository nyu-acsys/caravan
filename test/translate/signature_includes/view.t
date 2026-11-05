  $ caravan --shh view.ml
  Verification successful.

  $ caravan --shh view_wrong.ml 2>&1 | sed -n '/Type Error:/p'
  Type Error: The predicate cell is defined with other parameter types than it is declared with.

  $ caravan --shh view_defined.ml 2>&1 | sed -n '/Unsupported Error:/p'
  Unsupported Error: An inherited predicate definition in a module interface is not supported yet.
