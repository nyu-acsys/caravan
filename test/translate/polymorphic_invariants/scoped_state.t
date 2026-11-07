Actual state arguments use the caller's types, while declared fields keep their defining scope.

  $ caravan --shh scoped_state.ml
  Verification successful.
  $ caravan --shh --emit-rav scoped_state.ml > scoped_state.rav
  $ raven --shh scoped_state.rav
  Verification successful.
