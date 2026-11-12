Spawn inherits frozen visibility while preserving the parent's knowledge. Join
imports the child's completion visibility, including exceptional outcomes.
Native tasks retain ordinary resource ownership and support generic workers.

  $ caravan --shh domains.ml
  Verification successful.
  $ caravan --shh domains_generic.ml
  Verification successful.
  $ caravan --shh --emit-rav domains.ml > domains.rav
  $ raven --shh domains.rav
  Verification successful.

The same handoff supports combined execution components without transferring
held locks to a child.

  $ cp domains.ml combined.ml
  $ cat domains.proof > combined.proof
  $ cat >> combined.proof <<'PROOF'
  > module Resource : Ghost.MutexResource with type t = unit = struct
  >   type t = unit
  >   predicate resource (value : t) = true
  > end
  > module Guard = Ghost.Mutex (Resource)
  > PROOF
  $ caravan --shh combined.ml
  Verification successful.

Synchronization does not duplicate linear resources or forge visibility, and a
join handle can be consumed only once.

  $ caravan --shh domains_linear_fail.ml > linear.out 2>&1
  [1]
  $ grep -q 'Verification Error: A precondition may not hold' linear.out
  $ caravan --shh domains_missing_visibility_fail.ml > missing.out 2>&1
  [1]
  $ grep -q 'Verification Error: A precondition may not hold' missing.out
  $ caravan --shh domains_duplicate_join_fail.ml > duplicate.out 2>&1
  [1]
  $ grep -q 'Verification Error: A precondition may not hold' duplicate.out
