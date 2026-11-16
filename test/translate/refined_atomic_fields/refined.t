A constructor-refined atomic cell retains one heap identity across an ordinary
generic invariant and a separate GADT worker performing reads and compare-and-set.
The broader constructor set still admits Null.

  $ caravan --shh refined.ml
  Verification successful.
  $ caravan --shh --emit-rav refined.ml > refined.rav
  $ raven --shh refined.rav
  Verification successful.

The broader constructor set does not establish the narrower constructor constraint.

  $ cp refined.ml wrong.ml
  $ sed 's/ensures (result === Null)/ensures (result =\/= Null)/' refined.proof > wrong.proof
  $ caravan --shh wrong.ml > wrong.out 2>&1
  [1]
  $ grep -q 'Verification Error:' wrong.out
  $ grep -qi timeout wrong.out
  [1]
