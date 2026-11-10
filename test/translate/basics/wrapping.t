Executable integer operations wrap at each intermediate result, including pure functions.
Specification arithmetic remains mathematical, and boundary for loops finish after one body.

  $ caravan --shh wrapping.ml
  Verification successful.
  $ caravan --shh --emit-rav wrapping.ml > wrapping.rav
  $ raven --shh wrapping.rav
  Verification successful.

An unrestricted mathematical addition postcondition does not describe wrapped addition.

  $ printf 'let bump x = x + 1\n(*@ result = bump x ensures result = x + 1 *)\n' > wrapping_unbounded_fail.ml
  $ ! caravan --shh wrapping_unbounded_fail.ml > unbounded.out 2>&1
  $ grep -q 'A postcondition may not hold' unbounded.out
