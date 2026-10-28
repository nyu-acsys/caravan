Sequence predicate arguments translate and typecheck with inferred sequence outputs.

  $ caravan --shh --emit-rav sequence_predicate.ml > sequence_predicate.rav
  $ raven --shh --typeonly sequence_predicate.rav
  Verification successful.

  $ caravan --shh sequence_predicate_bool_fail.ml 2>&1 | sed -n 's/^Type Error: This specification has type bool, but int is required.*/Rejected bool element/p'
  Rejected bool element

  $ caravan --shh sequence_predicate_list_fail.ml 2>&1 | sed -n 's/^Type Error: This specification has type int list.*/Rejected int list/p'
  Rejected int list
