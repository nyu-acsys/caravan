Publication retains the full journal and begins a separate eligible journal at the
current write. Acquired reads use that journal through an explicit wrapper.
Publication facts are persistent agreement resources, with no invariant mask.

  $ caravan --shh publication.ml
  Verification successful.
  $ caravan --shh --emit-rav publication.ml > publication.rav
  $ raven --shh publication.rav
  Verification successful.

Full state alone does not justify publication.

  $ cp publication.ml unowned.ml
  $ sed 's/requires (Capacity.private_state Ghost.self cell current writes)/requires (Capacity.state cell current writes)/g' publication.proof > unowned.proof
  $ caravan --shh unowned.ml > unowned.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' unowned.out
  $ grep -qi 'timeout' unowned.out
  [1]

An unrestricted read retains private observations, even when the caller has
acquired visibility. The stronger postcondition requires the published read rule.

  $ cp publication.ml unrestricted_fail.ml
  $ sed 's/at (cell.value) Ghost.published_scope/at (cell.value) Ghost.scope/g' publication.proof > unrestricted_fail.proof
  $ caravan --shh unrestricted_fail.ml > unrestricted_fail.out 2>&1
  [1]
  $ grep -q 'Verification Error:' unrestricted_fail.out
  $ grep -qi 'timeout' unrestricted_fail.out
  [1]

Acquiring an unrelated atomic location does not authorize a published read.

  $ sed '/let receive (channel : int Atomic.t) cell =/a\  let other = Atomic.make 1 in' publication.ml | sed 's/Atomic.get channel/Atomic.get other/' > wrong_channel.ml
  $ sed 's/at (Atomic.get channel)/at (Atomic.get other)/' publication.proof > wrong_channel.proof
  $ caravan --shh wrong_channel.ml > wrong_channel.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' wrong_channel.out
  $ grep -qi 'timeout' wrong_channel.out
  [1]

The existing Domain handoff protocol transfers publication visibility. Both the
parent and worker retain the persistent fact; no relaxed-field-specific task
wrapper is needed.

  $ caravan --shh publication_domains.ml
  Verification successful.
  $ caravan --shh --emit-rav publication_domains.ml > publication_domains.rav
  $ raven --shh publication_domains.rav
  Verification successful.

The publication cut is the current write marker. The successful link CAS has
already released that marker when the ghost publication step runs. Failed links
leave the node private so its value can be rewritten before a retry.
The publish_at_link source proof checks both paths and cut coverage.

  $ cp publication.ml premature.ml
  $ sed 's/if linked then begin/if true then begin/g' publication.proof > premature.proof
  $ caravan --shh premature.ml > premature.out 2>&1
  [1]
  $ grep -q 'A precondition may not hold' premature.out
  $ grep -qi 'timeout' premature.out
  [1]
