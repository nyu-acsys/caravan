Proof scopes cannot use values bound in a different flat match branch.

  $ caravan --shh match_binding_scope_leak_fail.ml
  [Error] File "match_binding_scope_leak_fail.ml", line 13, columns 25-29:
  13 |         assert (result = left);
                                ^^^^
  Type Error: Unbound name left.
  [1]
