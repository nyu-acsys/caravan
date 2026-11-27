An interface can declare that a public invariant lies within another. The definition
keeps the promise by declaring its ancestor, possibly through private invariants.

  $ caravan --shh invariant_regions_promise.ml
  Verification successful.

A definition without the promised ancestor is rejected.

  $ cp invariant_regions_promise.ml missing.ml
  $ cp invariant_regions_promise.mli missing.mli
  $ sed 's/\[@within root cell\] //' invariant_regions_promise.mlp > missing.mlp
  $ caravan --shh missing.ml > missing.out 2>&1
  [1]
  $ grep -q 'The interface declares leaf within root, but its definition declares no ancestor' missing.out

The promise may be kept through an invariant private to the implementation.

  $ cp invariant_regions_promise.ml private.ml
  $ cp invariant_regions_promise.mli private.mli
  $ sed -e 's/invariant root (cell : t) = leaf cell/invariant root (cell : t) = middle cell\ninvariant [@within root cell] middle (cell : t) = leaf cell/' \
  >   -e 's/\[@within root cell\] leaf/[@within middle cell] leaf/' \
  >   -e 's/fold leaf result;/fold leaf result;\n    fold middle result;/' \
  >   -e 's/unfold root cell;/unfold root cell;\n    unfold middle cell;/' \
  >   -e 's/    fold leaf cell;/    fold leaf cell;\n    fold middle cell;/' \
  >   invariant_regions_promise.mlp > private.mlp
  $ caravan --shh private.ml
  Verification successful.

A chain that reaches another invariant does not keep the promise.

  $ sed -e 's/\[@within root cell\] middle/[@within other cell] middle/' \
  >   -e 's/invariant root (cell : t) = middle cell/invariant root (cell : t) = middle cell\ninvariant other (cell : t) = true/' \
  >   private.mlp > elsewhere.mlp
  $ cp private.ml elsewhere.ml
  $ cp private.mli elsewhere.mli
  $ caravan --shh elsewhere.ml > elsewhere.out 2>&1
  [1]
  $ grep -q 'The definition of leaf does not lie within root as its interface declares' elsewhere.out

A client of an imported interface relies on its promise: a mask covering the root
covers the invariant within it.

  $ caravan --shh -I promise_lib promise_client.ml
  Verification successful.
