A generic declaration's heap layout and result predicates are reused by its
applications, including applicative instances with the same argument.

  $ caravan --shh result_signature_heap.ml
  Verification successful.
  $ caravan --shh --emit-rav result_signature_heap.ml > generated.rav
  $ grep -Ec '^[[:space:]]+proc method_keep(_[0-9]+)?\(' generated.rav
  1
