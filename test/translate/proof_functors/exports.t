Proof predicates and lemmas from two applications are available through their members.

  $ caravan --shh exports.ml
  Verification successful.

  $ caravan --shh --emit-rav exports.ml > exports.rav
  $ raven --shh exports.rav
  Verification successful.

The generic worker has one body while both applications expose its proof members.

  $ grep -c '^module Generic_Make_Cell' exports.rav
  1

A member of the first application rejects a cell from the second application.

  $ cp exports.ml exports_cross.ml
  $ cat exports.proof > exports_cross.proof
  $ printf '\nlemma cross_application (cell : Second.t) (n [@implicit] : int)\n  requires (First.wrapped cell n)\n  ensures (true) = ()\n' >> exports_cross.proof
  $ ! caravan --shh exports_cross.ml > exports_cross.out 2>&1
  $ grep -q 'Type Error:' exports_cross.out

A checked view makes the exported predicate opaque through the view and its alias.

  $ cp exports.ml exports_opaque.ml
  $ cat exports.proof > exports_opaque.proof
  $ printf '\nlemma opaque_unfold (cell : Public_alias.t) (n [@implicit] : int)\n  requires (Public_alias.wrapped cell n)\n  ensures (Public_alias.wrapped cell n) =\n  unfold Public_alias.wrapped cell n;\n  fold Public_alias.wrapped cell n\n' >> exports_opaque.proof
  $ ! caravan --shh exports_opaque.ml > exports_opaque.out 2>&1
  $ grep -F 'Type Error: The definition of this predicate is hidden by its module signature.' exports_opaque.out
  Type Error: The definition of this predicate is hidden by its module signature.

The checked view and its alias also hide the lemma.

  $ cp exports.ml exports_hidden.ml
  $ cat exports.proof > exports_hidden.proof
  $ printf '\nlemma hidden_lemma (cell : Public_alias.t) (n [@implicit] : int)\n  requires (Public_alias.wrapped cell n)\n  ensures (Public_alias.wrapped cell n) =\n  Public_alias.preserve cell\n' >> exports_hidden.proof
  $ ! caravan --shh exports_hidden.ml > exports_hidden.out 2>&1
  $ grep -F 'Type Error: Unknown lemma Public_alias.preserve.' exports_hidden.out
  Type Error: Unknown lemma Public_alias.preserve.

Repeated applications retain one worker and interchangeable applicative types.

  $ caravan --shh exports_repeated.ml
  Verification successful.
  $ caravan --shh --emit-rav exports_repeated.ml > repeated.rav
  $ raven --shh repeated.rav
  Verification successful.
  $ grep -c '^module Generic_Make_Cell' repeated.rav
  1

A checked argument retains its source type in exported proof members.

  $ caravan --shh exports_argument.ml
  Verification successful.
  $ cp exports_argument.ml exports_argument_cross.ml
  $ cat exports_argument.proof > exports_argument_cross.proof
  $ printf '\nlemma wrong_argument (cell : Actual.First.t) (n [@implicit] : int)\n  requires (Third.wrapped cell n)\n  ensures (true) = ()\n' >> exports_argument_cross.proof
  $ ! caravan --shh exports_argument_cross.ml > argument.out 2>&1
  $ grep -q 'Type Error:' argument.out

Enclosing signatures hide helpers from clients while allowing implementation proofs.

  $ caravan --shh exports_nested.ml
  Verification successful.
  $ caravan --shh --emit-rav exports_nested.ml > nested.rav
  $ raven --shh nested.rav
  Verification successful.
  $ cp exports_nested.ml exports_nested_hidden.ml
  $ cat exports_nested.proof > exports_nested_hidden.proof
  $ printf '\nlemma use_hidden (cell : Outer.Exported.t) (n [@implicit] : int)\n  requires (Outer.Exported.wrapped cell n)\n  ensures (Outer.Exported.wrapped cell n) = Outer.Exported.preserve cell\n' >> exports_nested_hidden.proof
  $ ! caravan --shh exports_nested_hidden.ml > nested.out 2>&1
  $ grep -F 'Type Error: Unknown lemma Outer.Exported.preserve.' nested.out
  Type Error: Unknown lemma Outer.Exported.preserve.
