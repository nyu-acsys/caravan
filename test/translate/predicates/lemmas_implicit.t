Implicit values come from ownership at proof and runtime lemma calls, and callers
can also provide the trailing values explicitly.

  $ caravan --shh lemmas_implicit.ml
  Verification successful.

An implicit parameter cannot precede an explicit one.

  $ caravan --shh lemmas_implicit_nontrailing.ml
  [Error] File "lemmas_implicit_nontrailing.proof", line 1, columns 43-47:
  1 | lemma malformed (value [@implicit] : int) (cell : int Atomic.t) = ()
                                                 ^^^^
  Type Error: Implicit lemma parameters must follow explicit parameters.
  [1]

Only recognized parameter attributes are accepted.

  $ caravan --shh lemmas_implicit_unknown_attribute.ml
  [Error] File "lemmas_implicit_unknown_attribute.proof", line 1, columns 23-34:
  1 | lemma malformed (value [@surprise] : int) = ()
                             ^^^^^^^^^^^
  Syntax Error: Only [@implicit] is supported on lemma parameters.
  [1]

Calls reject missing explicit arguments, excess arguments, and ill-typed overrides.

  $ caravan --shh lemmas_implicit_missing_argument.ml
  [Error] File "lemmas_implicit_missing_argument.proof", line 7, columns 15-19:
  7 |   let result = read in
                     ^^^^
  Type Error: Lemma read expects between 1 and 2 arguments.
  [1]

  $ caravan --shh lemmas_implicit_wrong_arity.ml
  [Error] File "lemmas_implicit_wrong_arity.proof", line 5, columns 15-35:
  5 |   let result = identity value value in
                     ^^^^^^^^^^^^^^^^^^^^
  Type Error: Lemma identity expects between 0 and 1 arguments.
  [1]

  $ caravan --shh lemmas_implicit_wrong_type.ml
  [Error] File "lemmas_implicit_wrong_type.proof", line 5, columns 24-29:
  5 |   let result = identity value in
                              ^^^^^
  Type Error: The value value has type bool but an expression was expected of type int.
  [1]

Reference element types are checked before the Raven representation erases them.

  $ caravan --shh lemmas_implicit_wrong_reference_type.ml
  [Error] File "lemmas_implicit_wrong_reference_type.proof", line 5, columns 24-29:
  5 |   let result = identity value in
                              ^^^^^
  Type Error: The value value has type bool ref but an expression was expected of type
    int ref
  Type bool is not compatible with type int.
  [1]

Inference fails when no ownership identifies the missing value.

  $ caravan --shh lemmas_implicit_unowned.ml
  [Error] File "lemmas_implicit_unowned.proof", line 8, columns 15-24:
  8 |   let result = read cell in
                     ^^^^^^^^^
  Verification Error: A precondition may not hold for this call.
  File "lemmas_implicit_unowned.proof", line 3, columns 12-26:
  3 |   requires (own cell value)
                  ^^^^^^^^^^^^^^
  Related Location: This own predicate may not hold.
  [1]
