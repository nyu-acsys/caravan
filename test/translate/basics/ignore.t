Discarding an atomic operation's result retains its effects.

  $ caravan --shh ignore.ml
  Verification successful.

The discarded operation still changes the cell.

  $ cp ignore.ml unchanged.ml
  $ sed 's/ensures (own cell false)/ensures (own cell true)/' ignore.proof > unchanged.proof
  $ caravan --shh unchanged.ml > unchanged.out 2>&1
  [1]
  $ grep -q 'Verification Error:' unchanged.out
  $ grep -qi timeout unchanged.out
  [1]
