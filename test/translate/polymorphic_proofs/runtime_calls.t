Generic proof workers may call source functions through the existing dictionaries;
module instance dependencies are declared before the workers that use them.
Generic runtime workers can also invoke generic lemmas from ghost annotations.

  $ caravan --shh runtime_calls.ml
  Verification successful.
  $ caravan --shh --emit-rav runtime_calls.ml > runtime_calls.rav
  $ raven --shh runtime_calls.rav
  Verification successful.
