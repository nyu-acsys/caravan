An alias does not expose a lemma hidden by an explicit module signature.

  $ caravan --shh hidden_lemma_alias_fail.ml 2>&1 | grep -F 'Type Error: Unknown lemma Alias.hidden.'
  Type Error: Unknown lemma Alias.hidden.

The body of a public predicate is opaque behind an explicit module signature.

  $ caravan --shh opaque_unfold_fail.ml 2>&1 | grep -F 'Type Error: The definition of this predicate is hidden by its module signature.'
  Type Error: The definition of this predicate is hidden by its module signature.

Nominally distinct sibling module types cannot be exchanged through proof calls.

  $ caravan --shh sibling_nominal_fail.ml 2>&1 | grep -F 'This specification has type Right.t, but Left.t is required.'
  Type Error: This specification has type Right.t, but Left.t is required.

Scoped recursive lemmas require a variant.

  $ caravan --shh scoped_recursion_fail.ml 2>&1 | grep -F 'Type Error: A recursive lemma needs a variant.'
  Type Error: A recursive lemma needs a variant.
