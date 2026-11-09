Native conditions have a distinct OCaml type and preserve normalized aliases.

  $ caravan --shh allocation.ml
  Verification successful.

Wait releases and reacquires a protected resource; notification does not require
holding its associated mutex and supplies no protected data.

  $ caravan --shh basic.ml
  Verification successful.
  $ caravan --shh --emit-rav basic.ml > basic.rav
  $ raven --shh basic.rav
  Verification successful.

Condition associations and execution contexts pass through functors and Domain tasks.

  $ caravan --shh functor.ml
  Verification successful.
  $ caravan --shh --emit-rav functor.ml > functor.rav
  $ raven --shh functor.rav
  Verification successful.
