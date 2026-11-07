A constant user-defined algebra lifts pointwise alongside a parameterized algebra.

  $ caravan --shh resource_product.ml
  Verification successful.
  $ caravan --shh --emit-rav resource_product.ml > resource_product.rav
  $ raven --shh resource_product.rav
  Verification successful.
