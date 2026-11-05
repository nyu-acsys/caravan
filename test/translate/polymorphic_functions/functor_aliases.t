Aliases exported by a source functor retain one shared function body.

  $ caravan --shh functor_aliases.ml
  Verification successful.
  $ caravan --shh --emit-rav functor_aliases.ml > functor_aliases.rav
  $ grep -c '^module Generic_' functor_aliases.rav
  1
  $ grep -c '^  module Poly_.*_id_' functor_aliases.rav
  1
  $ ! grep -q '^module Poly_[^ ]*\[' functor_aliases.rav
  $ raven --shh functor_aliases.rav
  Verification successful.
