An imported include resolves its provider even when it sorts after the including file.
Included contracts retain ordinary and atomic resource channels, and repeated named
signatures keep their abstract types and predicates separate.

  $ caravan --shh client.ml
  Verification successful.

  $ caravan --shh --emit-rav client.ml > emitted.rav
  $ raven --shh --typeonly emitted.rav
  Verification successful.
