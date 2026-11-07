An implicit footprint can be duplicated through recursive predicate agreement.

  $ caravan --shh predicates_recursive_agreement.ml
  Verification successful.

An unconstrained recursive base case does not establish agreement.

  $ caravan --shh predicates_recursive_agreement_bad_base.ml
  [Error] File "predicates_recursive_agreement_bad_base.proof", line 2, columns 5-10:
  2 |     (cells [@implicit] : int Atomic.t finset) =
           ^^^^^
  Verification Error: Two instances held at the same time that agree on the explicit parameters may disagree on this implicit parameter.
  File "predicates_recursive_agreement_bad_base.proof", line 3, column 2 to line 8, column 60:
  3 |   match nodes with
        ^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]

Keeping the child's footprint explicit hides the agreement needed by an implicit
wrapper.

  $ caravan --shh predicates_recursive_agreement_explicit_child.ml
  [Error] File "predicates_recursive_agreement_explicit_child.proof", line 11, columns 5-10:
  11 |     (cells [@implicit] : int Atomic.t finset) =
            ^^^^^
  Verification Error: Two instances held at the same time that agree on the explicit parameters may disagree on this implicit parameter.
  File "predicates_recursive_agreement_explicit_child.proof", line 12, columns 2-23:
  12 |   footprint nodes cells
         ^^^^^^^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
