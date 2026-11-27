Generic functor proof models retain their constructors and pure functions at each application.

  $ caravan --shh models.ml
  Verification successful.
  $ caravan --shh --emit-rav models.ml > models.rav
  $ raven --shh models.rav
  Verification successful.
  $ grep -c 'Generic_Make_Cell\[Parameter:' models.rav
  1
  $ grep -c 'func make_singleton(' models.rav
  1
  $ grep -c 'module Make_Model' models.rav
  1

The first application and its alias share a model, including through a repeated application.

  $ cp models.ml models_cross.ml
  $ cat models.mlp > models_cross.mlp
  $ printf '\nlemma incompatible (cell : Second.t)\n  ensures (First.is_empty (Second.singleton cell) = false) = ()\n' >> models_cross.mlp
  $ ! caravan --shh models_cross.ml > models_cross.out 2>&1
  $ grep -q 'Type Error:' models_cross.out

A checked result hides the model type, function, and constructor.

  $ cp models.ml models_hidden_type.ml
  $ cat models.mlp > models_hidden_type.mlp
  $ printf '\nlemma hidden_type (cell : Sealed.t) ensures (true) =\n  let (value : Sealed.model) = First.singleton cell in ()\n' >> models_hidden_type.mlp
  $ ! caravan --shh models_hidden_type.ml > models_hidden_type.out 2>&1
  $ grep -F 'Unbound type constructor Sealed.model.' models_hidden_type.out
  Type Error: Unbound type constructor Sealed.model.

  $ cp models.ml models_hidden_function.ml
  $ cat models.mlp > models_hidden_function.mlp
  $ printf '\nlemma hidden_function (cell : Sealed.t) ensures (true) =\n  let (value : First.model) = Sealed.singleton cell in ()\n' >> models_hidden_function.mlp
  $ ! caravan --shh models_hidden_function.ml > models_hidden_function.out 2>&1
  $ grep -q 'Type Error:' models_hidden_function.out

  $ cp models.ml models_hidden_constructor.ml
  $ cat models.mlp > models_hidden_constructor.mlp
  $ printf '\nlemma hidden_constructor (cell : Sealed.t) ensures (true) =\n  let (value : First.model) = Sealed.Item cell in ()\n' >> models_hidden_constructor.mlp
  $ ! caravan --shh models_hidden_constructor.ml > models_hidden_constructor.out 2>&1
  $ grep -q 'Type Error:' models_hidden_constructor.out

An incorrect model function or generic lemma is rejected.

  $ cp models.ml models_bad_function.ml
  $ sed 's/Item _ -> false/Item _ -> true/' models.mlp > models_bad_function.mlp
  $ ! caravan --shh models_bad_function.ml > models_bad_function.out 2>&1
  $ grep -q 'Verification Error:' models_bad_function.out

  $ cp models.ml models_false_lemma.ml
  $ sed 's/singleton cell = Item cell && is_empty (singleton cell) = false/false/' models.mlp > models_false_lemma.mlp
  $ ! caravan --shh models_false_lemma.ml > models_false_lemma.out 2>&1
  $ grep -q 'Verification Error:' models_false_lemma.out

Generic logical functions remain declaration ordered and nonrecursive.

  $ cp models.ml models_forward.ml
  $ sed '/  type model = Empty | Item of Cell.t/a\
  >   let premature (cell : Cell.t) : bool = is_empty (Item cell)' models.mlp > models_forward.mlp
  $ ! caravan --shh models_forward.ml > models_forward.out 2>&1
  $ grep -F 'A logical function can only call earlier logical definitions.' models_forward.out
  Type Error: A logical function can only call earlier logical definitions.

  $ cp models.ml models_recursive.ml
  $ sed '/  type model = Empty | Item of Cell.t/a\
  >   let circular (cell : Cell.t) : model = circular cell' models.mlp > models_recursive.mlp
  $ ! caravan --shh models_recursive.ml > models_recursive.out 2>&1
  $ grep -F 'A logical function can only call earlier logical definitions.' models_recursive.out
  Type Error: A logical function can only call earlier logical definitions.
