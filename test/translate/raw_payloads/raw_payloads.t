Raw relaxed fields use the existing journals over options. A cleared word has no
ordinary source validity; aliases retain the same obligation. The generic
validation protocol checks a later atomic head observation before using a payload.

  $ caravan --shh --emit-rav validation.ml > validation.rav
  $ raven --shh validation.rav
  Verification successful.
  $ caravan --shh shadowed_cast.ml
  Verification successful.
  $ caravan --shh modules.ml
  Verification successful.
  $ caravan --shh -I imports imports.ml
  Verification successful.

Ignoring the validation result cannot justify returning the payload.

  $ sed 's/if Atomic.get head then None else Some value/if Atomic.get head then Some value else Some value/' validation.ml > unchecked.ml
  $ cp validation.mlp unchecked.mlp
  $ caravan --shh unchecked.ml > unchecked.out 2>&1
  [1]
  $ grep -q 'This speculative value may be cleared' unchecked.out
  $ grep -qi 'timeout' unchecked.out
  [1]

The proof needs the invariant connecting retirement to a head that cannot return.

  $ cp validation.ml aba.ml
  $ sed 's/(Set.mem true phases -> moved)/true/' validation.mlp > aba.mlp
  $ caravan --shh aba.ml > aba.out 2>&1
  [1]
  $ grep -q 'Verification Error:' aba.out
  $ grep -qi 'timeout' aba.out
  [1]

Clearing before retirement does not preserve the invariant.

  $ sed 's/Atomic.set head true/Atomic.set head false/g' validation.ml > early.ml
  $ sed 's/at (Atomic.set head true)/at (Atomic.set head false)/g' validation.mlp > early.mlp
  $ caravan --shh early.ml > early.out 2>&1
  [1]
  $ grep -q 'Verification Error:' early.out
  $ grep -qi 'timeout' early.out
  [1]
