Triggers of quantifiers and of auto lemmas' postconditions reach Raven.

  $ caravan --shh triggers.ml
  Verification successful.
  $ caravan --shh --emit-rav triggers.ml > triggers.rav
  $ grep -c 'ensures {Generic.len' triggers.rav
  1
  $ raven --shh --typeonly triggers.rav
  Verification successful.

Only an auto lemma's postconditions have triggers, and each trigger mentions every
parameter.

  $ caravan --shh manual_fail.ml
  [Error] File "manual_fail.proof", line 8, columns 10-23:
  8 |   ensures [len values]. (len values >= 0)
                ^^^^^^^^^^^^^
  Syntax Error: Only an auto lemma's postconditions have triggers.
  [1]
  $ caravan --shh partial_fail.ml
  [Error] File "partial_fail.proof", line 9, columns 11-21:
  9 |   ensures [len values]. (len values <= bound) =
                 ^^^^^^^^^^
  Type Error: This trigger does not mention the parameter bound.
  [1]

A quantified fact is instantiated only by terms matching its trigger.

  $ caravan --shh unmatched_fail.ml
  [Error] File "unmatched_fail.ml", line 2, columns 36-36:
  2 | let bounded (values : int list) = ()
                                          ^
  Verification Error: A postcondition may not hold at this return point.
  File "unmatched_fail.ml", line 5, columns 12-27:
  5 |     ensures len values <= 5 *)
                  ^^^^^^^^^^^^^^^
  Related Location: This assertion may not hold.
  [1]
