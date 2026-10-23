Imported atomic contracts preserve ordinary and atomic resource channels.

  $ caravan --shh client.ml
  Verification successful.

Imported atomic accesses use Raven's existing invariant and abort checks.

  $ caravan --shh protected.ml
  Verification successful.
