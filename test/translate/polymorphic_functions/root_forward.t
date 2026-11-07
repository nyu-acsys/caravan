Root function workers follow the module applications they capture, including
ordinary calls and transitive captures by subsequent generic module workers.

  $ caravan --shh root_forward.ml
  Verification successful.
  $ caravan --shh --emit-rav root_forward.ml > root_forward.rav
  $ raven --shh root_forward.rav
  Verification successful.
