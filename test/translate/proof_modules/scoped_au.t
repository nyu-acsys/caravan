Scoped and root-qualified AU facades retain operation and token identities.

  $ caravan --shh scoped_au.ml
  Verification successful.
  $ caravan --shh --emit-rav scoped_au.ml > scoped_au.rav
  $ raven --shh scoped_au.rav
  Verification successful.

A module-owned helping proof stores and recovers its AU token in ghost storage.

  $ caravan --shh scoped_au_help.ml
  Verification successful.
  $ caravan --shh --emit-rav scoped_au_help.ml > scoped_au_help.rav
  $ raven --shh scoped_au_help.rav
  Verification successful.

Qualified operation facades preserve opaque source types at their public boundary.

  $ caravan --shh scoped_au_opaque.ml
  Verification successful.
  $ caravan --shh --emit-rav scoped_au_opaque.ml > scoped_au_opaque.rav
  $ raven --shh scoped_au_opaque.rav
  Verification successful.

A root facade can target a qualified implementation without an extra module proof block.

  $ caravan --shh scoped_au_root.ml
  Verification successful.

A facade still requires a local operation with a logically atomic contract.

  $ caravan --shh scoped_au_ordinary.ml 2>&1 | grep -F 'Type Error: An AU facade requires a logically atomic contract.'
  Type Error: An AU facade requires a logically atomic contract.

Binding is restricted to the facade's operation.

  $ caravan --shh scoped_au_wrong_bind.ml 2>&1 | grep -F 'Type Error: An AU token can only be bound in its own procedure.'
  Type Error: An AU token can only be bound in its own procedure.

Raven continues to check token lifecycle errors after qualified lookup.

  $ caravan --shh scoped_au_double_open.ml 2>&1 | grep -F 'Verification Error: Atomic token token is already open.'
  Verification Error: Atomic token token is already open.

A checked contract view cannot be silently replaced by the underlying procedure.

  $ caravan --shh scoped_au_checked.ml 2>&1 | grep -F 'Type Error: An AU facade must name a procedure in this implementation.'
  Type Error: An AU facade must name a procedure in this implementation.
