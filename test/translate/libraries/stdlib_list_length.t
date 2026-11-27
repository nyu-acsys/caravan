Runtime list length uses a bounded int contract for empty, nonempty, and generic lists.
Specifications retain total mathematical length and respect local shadowing.

  $ caravan --shh stdlib_list_length.ml
  Verification successful.
  $ caravan --shh --emit-rav stdlib_list_length.ml > stdlib_list_length.rav
  $ raven --shh stdlib_list_length.rav
  Verification successful.

A runtime call requires the mathematical length to fit in an OCaml int.

  $ caravan --shh stdlib_list_length_fail.ml > unchecked.out 2>&1
  [1]
  $ grep 'Verification Error:' unchecked.out
  Verification Error: A precondition may not hold for this call.
