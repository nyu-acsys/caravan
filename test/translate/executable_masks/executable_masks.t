Executable masks bound nested invariant needs and survive imported and generic calls.

  $ caravan --shh closed.ml
  Verification successful.
  $ caravan --shh -I imports imported.ml
  Verification successful.
  $ caravan --shh generic.ml
  Verification successful.

An explicitly closed procedure cannot open its precondition invariant.

  $ sed 's/opens { shared cell Ghost.self; Value.frozen }/opens {}/' closed.proof > closed_fail.proof
  $ cp closed.ml closed_fail.ml
  $ caravan --shh --only read_shared closed_fail.ml > closed_fail.out 2>&1
  [1]
  $ grep -q 'Verification Error:' closed_fail.out
  $ grep -qi 'timeout' closed_fail.out
  [1]

An imported callee's mask is checked at the call, including adapter procedures.

  $ sed 's/opens { Reader.live cell }/opens {}/' imported.ml > imported_fail.ml
  $ caravan --shh -I imports imported_fail.ml > imported_fail.out 2>&1
  [1]
  $ grep -q 'Verification Error:' imported_fail.out
  $ grep -qi 'timeout' imported_fail.out
  [1]

Module compliance cannot weaken the implementation's invariant footprint.

  $ sed '0,/opens { live cell }/s//opens {}/' generic.ml > generic_fail.ml
  $ cp generic.proof generic_fail.proof
  $ caravan --shh generic_fail.ml > generic_fail.out 2>&1
  [1]
  $ grep -q 'Verification Error:' generic_fail.out
  $ grep -qi 'timeout' generic_fail.out
  [1]

Mask entries must name resources, and incompatible attribute clauses are rejected.

  $ caravan --shh nonresource_fail.ml > nonresource_fail.out 2>&1
  [1]
  $ grep -q 'Unknown resource in opens clause' nonresource_fail.out
  $ caravan --shh -I attribute_imports attribute_fail.ml > attribute_fail.out 2>&1
  [1]
  $ grep -q "opens clause conflicts with the signature's empty opens attribute" attribute_fail.out
