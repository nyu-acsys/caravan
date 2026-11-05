Proof matches retain the source restrictions on witness-selected reference results.

  $ caravan --shh witness_equality.ml
  Verification successful.

  $ mkdir structural
  $ cp witness_equality.ml structural/
  $ sed 's/result === result/result = result/' witness_equality.proof > structural/witness_equality.proof
  $ caravan --shh structural/witness_equality.ml
  [Error] File "structural/witness_equality.proof", line 5, columns 26-27:
  5 |   | Ref -> assert (result = result)
                                ^
  Type Error: Structural equality on references is unsupported; use == or != for reference identity.
  [1]
