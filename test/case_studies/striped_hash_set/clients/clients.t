The abstract contracts account for collisions, duplicate insertion, missing-key
removal, distinct stripes, and preservation across repeated and stale resize requests.

  $ caravan --shh clients.ml
  Verification successful.

A duplicate insertion must report that the key was already present.

  $ sed 's/assert (not (Striped_hash_set.add set 1))/assert (Striped_hash_set.add set 1)/' clients.ml > duplicate.ml
  $ cp clients.proof duplicate.proof
  $ caravan --shh duplicate.ml > duplicate.out 2>&1
  [1]
  $ grep -q 'Verification Error:' duplicate.out
  $ grep -qi 'timeout' duplicate.out
  [1]

A resize request must have a positive expected capacity.

  $ sed 's/Striped_hash_set.resize set 1/Striped_hash_set.resize set 0/' clients.ml > invalid_capacity.ml
  $ cp clients.proof invalid_capacity.proof
  $ caravan --shh invalid_capacity.ml > invalid_capacity.out 2>&1
  [1]
  $ grep -q 'Verification Error: A precondition may not hold' invalid_capacity.out
  $ grep -qi 'timeout' invalid_capacity.out
  [1]
