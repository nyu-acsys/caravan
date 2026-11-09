A park with the wrong guard cannot consume an available permit.

  $ sed 's/while not self.permit do/while self.permit do/' parker_.ml > wrong_guard.ml
  $ cp parker_.proof wrong_guard.proof
  $ caravan --shh wrong_guard.ml > wrong_guard.out 2>&1
  [1]
  $ grep -m1 -o 'This assertion may be violated' wrong_guard.out
  This assertion may be violated

A park must clear the physical permit before publishing its abstract update.

  $ sed 's/self.permit <- false/self.permit <- true/' parker_.ml > no_clear.ml
  $ cp parker_.proof no_clear.proof
  $ caravan --shh no_clear.ml > no_clear.out 2>&1
  [1]
  $ grep -m1 'Verification Error:' no_clear.out | sed 's/^.*Verification Error: /Verification Error: /'
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.

An unpark must install the permit before publishing its abstract update.

  $ sed 's/self.permit <- true/self.permit <- false/' parker_.ml > no_permit.ml
  $ cp parker_.proof no_permit.proof
  $ caravan --shh no_permit.ml > no_permit.out 2>&1
  [1]
  $ grep -m1 'Verification Error:' no_permit.out | sed 's/^.*Verification Error: /Verification Error: /'
  Verification Error: Failed to fold predicate. The body of the predicate may not hold at this point.
