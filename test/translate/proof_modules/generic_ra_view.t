An automatic view observes an abstract RA carrier as a value.

  $ caravan --shh generic_ra_view.ml
  Verification successful.
  $ caravan --shh --emit-rav generic_ra_view.ml > generic_ra_view.rav
  $ raven --shh generic_ra_view.rav
  Verification successful.
