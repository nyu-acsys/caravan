Proof headers mirror existing implementation definitions.

  $ caravan --shh owners.ml
  Verification successful.

Scoped proof bodies must not be silently ignored before their translation is supported.

  $ cp owners.ml scoped_body_fail.ml
  $ caravan --shh scoped_body_fail.ml
  [Error] File "scoped_body_fail.proof", line 2, columns 8-18:
  2 |   lemma impossible ensures (false) = ()
              ^^^^^^^^^^
  Unsupported Error: A proof declaration inside a source module is not supported yet.
  [1]
