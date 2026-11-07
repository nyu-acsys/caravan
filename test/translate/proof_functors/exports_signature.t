A result signature exposes its predicate with nominal result types.

  $ caravan --shh exports_signature.ml
  Verification successful.
  $ caravan --shh --emit-rav exports_signature.ml > signature.rav
  $ raven --shh signature.rav
  Verification successful.

The predicate definition is opaque, and the implementation lemma is hidden.

  $ cp exports_signature.ml exports_signature_opaque.ml
  $ cat exports_signature.proof > exports_signature_opaque.proof
  $ printf '\nlemma open_sealed (cell : Sealed.t) (n [@implicit] : int)\n  requires (Sealed.wrapped cell n)\n  ensures (Sealed.wrapped cell n) =\n  unfold Sealed.wrapped cell n; fold Sealed.wrapped cell n\n' >> exports_signature_opaque.proof
  $ ! caravan --shh exports_signature_opaque.ml > opaque.out 2>&1
  $ grep -F 'Type Error: The definition of this predicate is hidden by its module signature.' opaque.out
  Type Error: The definition of this predicate is hidden by its module signature.

  $ cp exports_signature.ml exports_signature_hidden.ml
  $ cat exports_signature.proof > exports_signature_hidden.proof
  $ printf '\nlemma use_hidden (cell : Alias.t) (n [@implicit] : int)\n  requires (Alias.wrapped cell n)\n  ensures (Alias.wrapped cell n) = Alias.preserve cell\n' >> exports_signature_hidden.proof
  $ ! caravan --shh exports_signature_hidden.ml > hidden.out 2>&1
  $ grep -F 'Type Error: Unknown lemma Alias.preserve.' hidden.out
  Type Error: Unknown lemma Alias.preserve.

Signature kind, source parameter types and implicit parameters must agree with the template.

  $ cp exports_signature.proof exports_signature_kind.proof
  $ sed -e '/^module Sealed/,/^end =/ s/predicate wrapped/invariant wrapped/' -e '/^module Sealed/,/^end =/ s/ \[@implicit\]//' exports_signature.ml > exports_signature_kind.ml
  $ ! caravan --shh exports_signature_kind.ml > kind.out 2>&1
  $ grep -F 'Type Error: The module resource has a different predicate or invariant kind.' kind.out
  Type Error: The module resource has a different predicate or invariant kind.

  $ cp exports_signature.proof exports_signature_type.proof
  $ sed '/^module Sealed/,/^end =/ s/: int)/: bool)/' exports_signature.ml > exports_signature_type.ml
  $ ! caravan --shh exports_signature_type.ml > type.out 2>&1
  $ grep -F 'Type Error: The module resource has different parameter types.' type.out
  Type Error: The module resource has different parameter types.

  $ cp exports_signature.proof exports_signature_mode.proof
  $ sed '/^module Sealed/,/^end =/ s/ \[@implicit\]//' exports_signature.ml > exports_signature_mode.ml
  $ ! caravan --shh exports_signature_mode.ml > mode.out 2>&1
  $ grep -F 'Type Error: The module resource has different implicit parameters.' mode.out
  Type Error: The module resource has different implicit parameters.

A compilation-unit interface checks each named application independently.

  $ caravan --shh exports_interface.ml
  Verification successful.
