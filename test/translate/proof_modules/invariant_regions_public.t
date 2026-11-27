A public invariant can be declared within another only if its interface declares so.

  $ caravan --shh invariant_regions_public.ml > public.out 2>&1
  [1]
  $ grep -q 'An invariant that its interface does not declare within another cannot be declared within one' public.out
