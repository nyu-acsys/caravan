A step that opens by a lemma that another closes, and does not close itself, is
closed before its result, and before the invariants it opened are closed.

  $ caravan --shh counter.ml
  Verification successful.

Without the closing lemma, the step leaves the predicate open.

  $ sed 's/lemma \[@closes take\] put/lemma put/' counter.proof > unclosed.proof
  $ cp counter.ml unclosed.ml
  $ caravan --shh unclosed.ml
  [Error] File "unclosed.proof", line 17, columns 10-19:
  17 |   opens { counter c }
                 ^^^^^^^^^
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
  File "unclosed.proof", line 17, columns 10-19:
  17 |   opens { counter c }
                 ^^^^^^^^^
  Related Location: No witness could be computed for v, so the value from the unfold at line 17 was used.
  File "unclosed.proof", line 2, columns 55-63:
  2 | invariant counter (c : int Atomic.t) = exists v : int. cell c v && 0 <= v
                                                             ^^^^^^^^
  Related Location: This predicate may not hold.
  [1]
