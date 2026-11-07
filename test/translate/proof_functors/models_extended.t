Recursive ghost models and aliases share applicative types across nested applications.

  $ caravan --shh models_extended.ml
  Verification successful.
  $ caravan --shh --emit-rav models_extended.ml > models_extended.rav
  $ raven --shh models_extended.rav
  Verification successful.

A sealed functor result hides each ghost descriptor and pure helper.

  $ cp models_extended.ml models_extended_hidden_model.ml
  $ cat models_extended.proof > models_extended_hidden_model.proof
  $ printf '\nlemma hidden_model (cell : Hidden_first.t) =\n  let (value : Hidden_first.model) = First.singleton cell in ()\n' >> models_extended_hidden_model.proof
  $ ! caravan --shh models_extended_hidden_model.ml > models_extended_hidden_model.out 2>&1
  $ grep -F 'Unbound type constructor Hidden_first.model.' models_extended_hidden_model.out
  Type Error: Unbound type constructor Hidden_first.model.

  $ cp models_extended.ml models_extended_hidden_chain.ml
  $ cat models_extended.proof > models_extended_hidden_chain.proof
  $ printf '\nlemma hidden_chain (cell : Hidden_first.t) =\n  let (value : Hidden_first.chain) = First.Link (cell, First.End) in ()\n' >> models_extended_hidden_chain.proof
  $ ! caravan --shh models_extended_hidden_chain.ml > models_extended_hidden_chain.out 2>&1
  $ grep -F 'Unbound type constructor Hidden_first.chain.' models_extended_hidden_chain.out
  Type Error: Unbound type constructor Hidden_first.chain.

  $ cp models_extended.ml models_extended_hidden_function.ml
  $ cat models_extended.proof > models_extended_hidden_function.proof
  $ printf '\nlemma hidden_function (cell : Hidden_first.t) =\n  let (value : First.model) = Hidden_first.singleton cell in ()\n' >> models_extended_hidden_function.proof
  $ ! caravan --shh models_extended_hidden_function.ml > models_extended_hidden_function.out 2>&1
  $ grep -q 'Type Error:' models_extended_hidden_function.out

  $ cp models_extended.ml models_extended_hidden_constructor.ml
  $ cat models_extended.proof > models_extended_hidden_constructor.proof
  $ printf '\nlemma hidden_constructor (cell : Hidden_first.t) =\n  let (value : First.model) = Hidden_first.Item cell in ()\n' >> models_extended_hidden_constructor.proof
  $ ! caravan --shh models_extended_hidden_constructor.ml > models_extended_hidden_constructor.out 2>&1
  $ grep -q 'Type Error:' models_extended_hidden_constructor.out
