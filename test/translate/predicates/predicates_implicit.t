Reference valued and list valued outputs can be omitted or supplied explicitly.
The output of an owned predicate can be inferred at a checked lemma call.

  $ caravan --shh predicates_implicit.ml
  Verification successful.

Implicit predicate parameters must trail explicit parameters.

  $ caravan --shh predicates_implicit_nontrailing.ml
  [Error] File "predicates_implicit_nontrailing.proof", line 1, columns 47-51:
  1 | predicate malformed (value [@implicit] : int) (cell : int Atomic.t) = own cell value
                                                     ^^^^
  Type Error: Implicit predicate parameters must follow explicit parameters.
  [1]

Only the implicit parameter attribute is recognized.

  $ caravan --shh predicates_implicit_unknown_attribute.ml
  [Error] File "predicates_implicit_unknown_attribute.proof", line 1, columns 49-60:
  1 | predicate malformed (cell : int Atomic.t) (value [@surprise] : int) = own cell value
                                                       ^^^^^^^^^^^
  Syntax Error: Only [@implicit] is supported on predicate parameters.
  [1]

Raven checks that an implicit output is determined by the predicate body.

  $ caravan --shh predicates_implicit_agreement.ml
  [Error] File "predicates_implicit_agreement.proof", line 2, columns 5-10:
  2 |     (value [@implicit] : int Atomic.t) = true
           ^^^^^
  Verification Error: Two instances held at the same time that agree on the explicit parameters may disagree on this implicit parameter.
  File "predicates_implicit_agreement.proof", line 2, columns 41-45:
  2 |     (value [@implicit] : int Atomic.t) = true
                                               ^^^^
  Related Location: This assertion may not hold.
  [1]

Reference element types are checked before Raven erases them.

  $ caravan --shh predicates_implicit_wrong_call.ml
  [Error] File "predicates_implicit_wrong_call.proof", line 5, columns 20-25:
  5 |   assert (held cell value)
                          ^^^^^
  Type Error: The value value has type bool Atomic.t but an expression was expected of type
    int Atomic.t
  Type bool is not compatible with type int.
  [1]

  $ caravan --shh predicates_implicit_wrong_fold.ml
  [Error] File "predicates_implicit_wrong_fold.proof", line 5, columns 17-22:
  5 |   fold held cell value
                       ^^^^^
  Type Error: The value value has type bool Atomic.t but an expression was expected of type
    int Atomic.t
  Type bool is not compatible with type int.
  [1]

  $ caravan --shh predicates_implicit_wrong_unfold.ml
  [Error] File "predicates_implicit_wrong_unfold.proof", line 5, columns 19-24:
  5 |   unfold held cell value
                         ^^^^^
  Type Error: The value value has type bool Atomic.t but an expression was expected of type
    int Atomic.t
  Type bool is not compatible with type int.
  [1]

Predicate calls reject missing explicit inputs and excess arguments.

  $ caravan --shh predicates_implicit_missing_input.ml
  [Error] File "predicates_implicit_missing_input.proof", line 4, columns 19-23:
  4 | lemma wrong = fold held
                         ^^^^
  Type Error: Predicate held expects between 1 and 2 arguments.
  [1]

  $ caravan --shh predicates_implicit_too_many.ml
  [Error] File "predicates_implicit_too_many.proof", line 5, columns 7-28:
  5 |   fold held cell value value
             ^^^^^^^^^^^^^^^^^^^^^
  Type Error: Predicate held expects between 1 and 2 arguments.
  [1]

Declarations and definitions must agree on which predicate parameters are implicit.

  $ caravan --shh predicates_implicit_interface_mismatch.ml
  [Error] File "predicates_implicit_interface_mismatch.proof", line 1, columns 10-14:
  1 | predicate held (cell : int Atomic.t Atomic.t)
                ^^^^
  Type Error: The predicate held has different implicit parameters in its declaration and definition.
  File "predicates_implicit_interface_mismatch.mli", line 1, column 0 to line 2, column 43:
  1 | (*@ predicate held (cell : int Atomic.t Atomic.t)
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Related Location: Its declaration.
  [1]
