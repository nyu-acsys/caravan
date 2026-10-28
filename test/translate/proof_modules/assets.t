Module-owned resource instances and fields preserve identities through aliases.

  $ caravan --shh assets.ml
  Verification successful.
  $ caravan --shh --emit-rav assets.ml > assets.rav
  $ raven --shh assets.rav
  Verification successful.

Implementation annotations use the same scoped descriptors as proof lemmas.

  $ caravan --shh asset_storage.ml
  Verification successful.
