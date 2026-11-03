Generic invariant bodies serve named and unit functors with abstract result types,
repeated applications, aliases, and two payload types together.

  $ caravan --shh functor.ml
  Verification successful.
  $ caravan --shh --emit-rav functor.ml > functor.rav
  $ grep -c 'inv make_is_cell(' functor.rav
  1
  $ grep -c 'inv fresh_is_cell(' functor.rav
  1
  $ raven --shh functor.rav
  Verification successful.

The native generic payload remains rigid under a concrete cast.

  $ mkdir bad_cast
  $ cp functor.ml bad_cast/
  $ sed 's/value = value }/value = (value : bool) }/' functor.proof > bad_cast/functor.proof
  $ caravan --shh bad_cast/functor.ml > bad_cast.out 2>&1
  [1]
  $ grep -Eq 'Type Error:|Unsupported Error: This polymorphic function occurrence or signature alias is not supported yet' bad_cast.out
  $ ! grep -Eq 'Syntax Error:|Internal Error:' bad_cast.out
