Private invariant ancestry is checked under an opaque public root.

  $ caravan --shh invariant_regions.ml
  Verification successful.

Nesting a child assertion alone does not grant permission to open its invariant.

  $ cp invariant_regions.ml unrelated.ml
  $ cp invariant_regions.mli unrelated.mli
  $ sed 's/\[@within root cell\] //' invariant_regions.proof > unrelated.proof
  $ caravan --shh unrelated.ml > unrelated.out 2>&1
  [1]
  $ grep -q 'Invariant leaf is not in the current mask' unrelated.out

A public invariant can be declared within another only if its interface declares so.

  $ cp invariant_regions.ml public.ml
  $ cp invariant_regions.proof public.proof
  $ cat invariant_regions.mli > public.mli
  $ printf '\n(*@ invariant leaf (cell : t) *)\n' >> public.mli
  $ caravan --shh public.ml > public.out 2>&1
  [1]
  $ grep -q 'An invariant that its interface does not declare within another cannot be declared within one' public.out
