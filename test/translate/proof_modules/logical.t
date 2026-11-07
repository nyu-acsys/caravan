Scoped pure functions retain sibling identities and resolve through aliases.

  $ caravan --shh logical.ml
  Verification successful.
  $ caravan --shh --emit-rav logical.ml > logical.rav
  $ raven --shh logical.rav
  Verification successful.

Scoped algebraic models keep distinct constructor and type identities.

  $ caravan --shh logical_types.ml
  Verification successful.
  $ caravan --shh --emit-rav logical_types.ml > logical_types.rav
  $ raven --shh logical_types.rav
  Verification successful.

Logical functions remain nonrecursive and declaration ordered.

  $ caravan --shh logical_forward_fail.ml 2>&1 | grep -F 'A logical function can only call earlier logical definitions.'
  Type Error: A logical function can only call earlier logical definitions.

Pure definitions cannot use qualified predicates, including through aliases.

  $ caravan --shh logical_purity_fail.ml 2>&1 | grep -F 'A pure logical function cannot use ownership or predicates.'
  Type Error: A pure logical function cannot use ownership or predicates.

Ascribed modules keep their logical representation types private.

  $ caravan --shh logical_hidden_fail.ml 2>&1 | grep -F 'Unbound type constructor Alias.model.'
  Type Error: Unbound type constructor Alias.model.

Partial logical applications are rejected by the source type checker.

  $ caravan --shh logical_partial_fail.ml 2>&1 | grep -F 'Type Error: This expression has type int -> int'
  Type Error: This expression has type int -> int but an expression was expected of type

Sibling models are nominally distinct even when their constructors share names.

  $ cp logical_types.ml type_mismatch.ml
  $ cp logical_types_mismatch.proof type_mismatch.proof
  $ caravan --shh type_mismatch.ml 2>&1 | grep -F 'has type Right.model but an expression was expected of type'
  Type Error: The value value has type Right.model but an expression was expected of type

A sealed outer module permits internal qualified proof calls and unfolds.

  $ caravan --shh logical_sealed.ml
  Verification successful.
  $ caravan --shh --emit-rav logical_sealed.ml > logical_sealed.rav
  $ raven --shh logical_sealed.rav
  Verification successful.

The enclosing signature still hides these proof helpers from external clients.

  $ cp logical_sealed.ml logical_sealed_leak.ml
  $ cat logical_sealed.proof > logical_sealed_leak.proof
  $ printf '\nlemma leak (value : Outer.A.model) = ()\n' >> logical_sealed_leak.proof
  $ caravan --shh logical_sealed_leak.ml 2>&1 | grep -F 'Unbound type constructor Outer.A.model.'
  Type Error: Unbound type constructor Outer.A.model.
