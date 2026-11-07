Proof headers mirror existing implementation definitions.

  $ caravan --shh owners.ml
  Verification successful.

Scoped lemma bodies are verified.

  $ cp owners.ml scoped_body_fail.ml
  $ caravan --shh scoped_body_fail.ml
  [Error] File "scoped_body_fail.proof", line 2, columns 18-18:
  2 |   lemma impossible ensures (false) = ()
                        ^
  Verification Error: A postcondition may not hold at this return point.
  File "scoped_body_fail.proof", line 2, columns 28-33:
  2 |   lemma impossible ensures (false) = ()
                                  ^^^^^
  Related Location: This assertion may not hold.
  [1]
