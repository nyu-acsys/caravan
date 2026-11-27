Explicit exit contexts describe acquiring and releasing helper effects. Defaults
remain balanced independently on the normal exit and each exceptional exit.

  $ caravan --shh effects.ml
  Verification successful.
  $ caravan --shh --emit-rav effects.ml > effects.rav
  $ raven --shh effects.rav
  Verification successful.

A bare exceptional clause still preserves holdings on that outcome.

  $ cp effects.ml bare.ml
  $ sed 's/raises Unchanged n -> (Guard.is_mutex mutex cell \&\& n === 0)/raises Unchanged _/' effects.mlp > bare.mlp
  $ caravan --shh bare.ml
  Verification successful.

An explicit acquired set cannot be replaced by the unchanged entry set.

  $ cp effects.ml wrong_set.ml
  $ sed 's/Finset.union held (Finset.singleton mutex)/held/g' effects.mlp > wrong_set.mlp
  $ caravan --shh wrong_set.ml > wrong_set.out 2>&1
  [1]
  $ grep -q 'Verification Error: A postcondition may not hold' wrong_set.out

An explicit exceptional effect does not remove the normal preservation default.

  $ sed 's/raise (Acquired 1))/raise (Acquired 1)) else acquire mutex cell/' effects.ml > normal_leak.ml
  $ cp effects.mlp normal_leak.mlp
  $ caravan --shh normal_leak.ml > normal_leak.out 2>&1
  [1]
  $ grep -q 'Verification Error: A postcondition may not hold' normal_leak.out

Explicit effects on other outcomes do not remove an exceptional default.

  $ sed 's/if choice = 0 then raise (Unchanged choice);/if choice = 0 then (acquire mutex cell; raise (Unchanged choice));/' effects.ml > exceptional_leak.ml
  $ cp effects.mlp exceptional_leak.mlp
  $ caravan --shh exceptional_leak.ml > exceptional_leak.out 2>&1
  [1]
  $ grep -q 'Verification Error: A postcondition may not hold' exceptional_leak.out

An explicit exit context cannot change the actual execution owner.

  $ caravan --shh owner_post.ml > owner_post.out 2>&1
  [1]
  $ grep -q 'Verification Error: A postcondition may not hold' owner_post.out

Overlapping exception clauses impose all their contracts: a context-omitting
catch-all also requires preservation when a specific clause changes holdings.

  $ cp effects.ml overlap.ml
  $ sed 's/raises Unchanged n ->/raises _ raises Unchanged n ->/' effects.mlp > overlap.mlp
  $ caravan --shh overlap.ml > overlap.out 2>&1
  [1]
  $ grep -q 'Verification Error: A postcondition may not hold' overlap.out
