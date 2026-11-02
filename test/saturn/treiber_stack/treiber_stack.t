  $ caravan --shh -I ../backoff treiber_stack.ml
  Verification successful.

The same implementation and predicate worker serve integer and boolean clients.

  $ mkdir clients
  $ cp treiber_stack.ml treiber_stack.mli treiber_stack.proof clients/
  $ chmod u+w clients/treiber_stack.ml
  $ cat clients.ml >> clients/treiber_stack.ml
  $ caravan --shh -I ../backoff clients/treiber_stack.ml
  Verification successful.
