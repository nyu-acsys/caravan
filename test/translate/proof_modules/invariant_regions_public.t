A resource-only module signature cannot hide a public invariant's concrete parent.

  $ caravan --shh invariant_regions_public.ml > public.out 2>&1
  [1]
  $ grep -q 'Only a private invariant can declare a parent' public.out
