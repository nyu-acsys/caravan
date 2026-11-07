Ordinary mutable reads preserve fractional ownership; writes update full ownership.

  $ caravan --shh nonatomic_fractional.ml
  Verification successful.
