Pure helpers reuse their enclosing type dictionaries and receive captured values.
Captures include tuple-pattern projections and pure let-bound expressions.

  $ caravan --shh pure.ml
  Verification successful.
  $ caravan --shh --emit-rav pure.ml > pure.rav
  $ raven --shh pure.rav
  Verification successful.
