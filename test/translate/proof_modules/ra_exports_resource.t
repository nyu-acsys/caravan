An exported algebra carrier is available to public predicates and contracts.

  $ caravan --shh ra_exports_resource.ml
  Verification successful.
  $ caravan --shh --emit-rav ra_exports_resource.ml > ra_exports_resource.rav
  $ raven --shh ra_exports_resource.rav
  Verification successful.

The same public carrier is available through a separate source interface.

  $ caravan --shh ra_exports_resource_interface.ml
  Verification successful.
