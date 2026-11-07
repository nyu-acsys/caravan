State scopes thread ghost values through adjacent accesses. Branches, nested
expressions, loops, and ordinary access scopes preserve the enclosing state.

  $ caravan --shh manual_state.ml
  Verification successful.
