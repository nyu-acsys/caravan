Polymorphic functions share a functor when they use each other at their own type
parameters; nested calls wrap at another type, so it applies the shared functor.

  $ caravan --shh worker_groups.ml
  Verification successful.
  $ caravan --shh --emit-rav worker_groups.ml > worker_groups.rav
  $ python3 check_worker_groups.py worker_groups.rav
  $ raven --shh worker_groups.rav
  Verification successful.
