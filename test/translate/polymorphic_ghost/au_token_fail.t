AU tokens cannot be used at a different source type index.

  $ caravan --shh au_token_fail.ml
  [Error] File "au_token_fail.proof", line 5, columns 12-35:
  5 |   requires (Read.pending token cell) = ()
                  ^^^^^^^^^^^^^^^^^^^^^^^
  Unsupported Error: This polymorphic function occurrence or signature alias is not supported yet.
  [1]
