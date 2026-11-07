An own interface validates nested resources without hiding same-file proof helpers.

  $ caravan --shh own_interface.ml
  Verification successful.

A module signature may declare a resource but may not define it.

  $ caravan --shh resource_defined.ml > resource_defined.out 2>&1; status=$?; test "$status" -eq 1 && grep -F 'A resource definition in a module signature' resource_defined.out
  Unsupported Error: A resource definition in a module signature is not supported yet.
