Calls retain the declaration selected before a same-named function is rebound.

  $ caravan --shh path_shadowing.ml
  Verification successful.

Line directives do not move a trailing contract outside its physical source scope.

  $ cat > path_scope_remapped_fail.ml <<'EOF'
  > # 1 "remapped.ml"
  > let wrong () = 1
  > (*@ result = wrong () ensures result = 2 *)
  > EOF
  $ caravan --shh path_scope_remapped_fail.ml
  [Error] File "remapped.ml", line 1, columns 16-16:
  Verification Error: A postcondition may not hold at this return point.
  File "remapped.ml", line 2, columns 30-40:
  Related Location: This assertion may not hold.
  [1]
