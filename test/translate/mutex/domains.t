Child executions have fresh owners and empty holdings, independently of their
parent. Cleanup is checked on normal and exceptional completion.

  $ caravan --shh domain_critical.ml
  Verification successful.
  $ caravan --shh --emit-rav domain_critical.ml > domain_critical.rav
  $ raven --shh domain_critical.rav
  Verification successful.

A task's generic contract may allow an ownership-changing helper effect, but
its checked completion adapter must still prove empty holdings on every outcome.
This is checked even for facades that are never spawned.

  $ caravan --shh domain_leak.ml > leak.out 2>&1
  [1]
  $ grep -q 'Verification Error: A precondition may not hold' leak.out
  $ caravan --shh --emit-rav domain_leak.ml > leak.rav
  $ raven --shh leak.rav > emitted_leak.out 2>&1
  [1]
  $ grep -q 'Verification Error: A precondition may not hold' emitted_leak.out
  $ caravan --shh domain_exception_leak.ml > exceptional_leak.out 2>&1
  [1]
  $ grep -q 'Verification Error: A precondition may not hold' exceptional_leak.out

A parent-held token cannot supply a child's owner or held set.

  $ caravan --shh domain_release.ml > release.out 2>&1
  [1]
  $ grep -q 'Verification Error: A precondition may not hold' release.out

An explicit ghost input cannot select the parent as the child's execution owner.

  $ caravan --shh domain_owner.ml > owner.out 2>&1
  [1]
  $ grep -q 'Verification Error: A precondition may not hold' owner.out

Existing polymorphic, ghost-result and history tasks use the same lifecycle.

  $ caravan --shh domain_poly.ml
  Verification successful.
  $ caravan --shh --emit-rav domain_poly.ml > domain_poly.rav
  $ raven --shh domain_poly.rav
  Verification successful.
  $ caravan --shh domain_values.ml
  Verification successful.
  $ cp domain_poly.ml empty_entry.ml
  $ sed 's/Ghost.Mutex.context self held/Ghost.Mutex.context self Finset.empty/g; s/not (Finset.mem mutex held)/true/g' domain_poly.mlp > empty_entry.mlp
  $ caravan --shh empty_entry.ml
  Verification successful.
  $ cp ../domains/ghost_explicit.ml ghost.ml
  $ cat ../domains/ghost_explicit.mlp unit_resource.mlp > ghost.mlp
  $ caravan --shh ghost.ml
  Verification successful.
  $ cp ../domains/ghost_explicit_raises.ml ghost_raises.ml
  $ cat ../domains/ghost_explicit_raises.mlp unit_resource.mlp > ghost_raises.mlp
  $ caravan --shh ghost_raises.ml
  Verification successful.
  $ cp ../domains/history.ml history.ml
  $ cat ../domains/history.mlp unit_resource.mlp > history.mlp
  $ caravan --shh history.ml
  Verification successful.
