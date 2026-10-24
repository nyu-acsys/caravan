Explicit stateful reads compose inside a nested read chain. A compound expression
restores its enclosing state; a direct let continuation receives the outer output.

  $ caravan --shh manual_state_nested.ml
  Verification successful.
