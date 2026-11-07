Nested manual atomic updates resolve each scope's predicate and AU token.

  $ caravan --shh nested_au.ml
  Verification successful.
  $ caravan --shh --emit-rav nested_au.ml > nested_au.rav
  $ raven --shh nested_au.rav
  Verification successful.

Same-spelled facades for different operations have distinct source token types.

  $ cp nested_au.ml nested_au_wrong_token.ml
  $ caravan --shh nested_au_wrong_token.ml 2>&1 | grep -F 'Type Error: The value token has type Left.Read.token'
  Type Error: The value token has type Left.Read.token

The enclosing signature keeps facade token types private from clients.

  $ cp nested_au.ml nested_au_hidden_fail.ml
  $ caravan --shh nested_au_hidden_fail.ml 2>&1 | grep -F 'Type Error: Unbound module Outer.Left.Read.'
  Type Error: Unbound module Outer.Left.Read.
