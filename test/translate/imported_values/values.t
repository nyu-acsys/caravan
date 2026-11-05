Imported values retain their identity and provide duplicable facts on each read.
Local imported operations introduce no shared step, including when returning unit.

  $ caravan --shh client.ml
  Verification successful.
  $ caravan --shh --emit-rav client.ml > client.rav
  $ raven --shh client.rav
  Verification successful.

A repeated value lookup cannot grant consumable resources or require an action.

  $ mkdir consumable conditional
  $ cp client.ml client.mli client.proof operations.mli consumable/
  $ sed 's/invariant stable/predicate stable/' constants.mli > consumable/constants.mli
  $ caravan --shh consumable/client.ml > consumable.out 2>&1
  [1]
  $ grep -c 'An imported value contract granting consumable resources' consumable.out
  1
  $ cp client.ml client.mli client.proof operations.mli conditional/
  $ sed 's/ensures stable result/requires true ensures stable result/' constants.mli > conditional/constants.mli
  $ caravan --shh conditional/client.ml > conditional.out 2>&1
  [1]
  $ grep -c 'An imported value contract with preconditions, effects, or modifiers' conditional.out
  1

Local contracts grant only stable facts and use an explicit, payload-free attribute.

  $ mkdir local_resource local_precondition local_payload local_duplicate
  $ cp client.ml client.mli client.proof constants.mli local_resource/
  $ sed 's/invariant stable/predicate stable/' operations.mli > local_resource/operations.mli
  $ caravan --shh local_resource/client.ml > local_resource.out 2>&1
  [1]
  $ grep -c 'A local imported contract granting consumable resources' local_resource.out
  1
  $ cp client.ml client.mli client.proof constants.mli local_precondition/
  $ sed 's/ensures result = value/requires true ensures result = value/' operations.mli > local_precondition/operations.mli
  $ caravan --shh local_precondition/client.ml > local_precondition.out 2>&1
  [1]
  $ grep -c 'A local imported contract with preconditions, effects, or modifiers' local_precondition.out
  1
  $ cp client.ml client.mli client.proof constants.mli local_payload/
  $ sed 's/\[@@caravan.local\]/[@@caravan.local false]/' operations.mli > local_payload/operations.mli
  $ caravan --shh local_payload/client.ml > local_payload.out 2>&1
  [1]
  $ grep -c 'A local attribute other than a single' local_payload.out
  1
  $ cp client.ml client.mli client.proof constants.mli local_duplicate/
  $ sed 's/\[@@caravan.local\]/[@@caravan.local] [@@caravan.local]/' operations.mli > local_duplicate/operations.mli
  $ caravan --shh local_duplicate/client.ml > local_duplicate.out 2>&1
  [1]
  $ grep -c 'A local attribute other than a single' local_duplicate.out
  1

Source implementations cannot claim the trusted local-import effect restriction.

  $ caravan --shh sourcebody.ml > sourcebody.out 2>&1
  [1]
  $ grep -c 'The local attribute is supported only on trusted imports' sourcebody.out
  1

Raven enforces an explicit empty opens clause on a verified source implementation.
The same invariant-opening proof succeeds without that restriction.

  $ caravan --shh sourceopens.ml > sourceopens.out 2>&1
  [1]
  $ grep -q 'is not in the current mask' sourceopens.out
  $ mkdir unrestricted
  $ cp sourceopens.ml sourceopens.proof unrestricted/
  $ sed 's/ \[@@caravan.opens.*//' sourceopens.mli > unrestricted/sourceopens.mli
  $ caravan --shh unrestricted/sourceopens.ml
  Verification successful.
