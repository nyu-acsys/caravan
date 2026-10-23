Concrete allocations initialize explicit value and resource fields. Ghost-only
registrations support fractional reads and writes after recombining both halves.

  $ caravan --shh ghost_storage.ml
  Verification successful.
