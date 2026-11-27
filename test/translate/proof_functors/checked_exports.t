An opaque companion interface checks contracts of concrete functor instances and
native modules without replacing the implementation's existing contracts.

  $ caravan --shh checked_exports.ml
  Verification successful.

The exported view must follow from the existing implementation contract.

  $ cp checked_exports.ml incorrect_export.ml
  $ sed '/^module First/,/^end/ s/ensures result === x/ensures result === x + 1/' checked_exports.mli > incorrect_export.mli
  $ caravan --shh incorrect_export.ml > incorrect.out 2>&1
  [1]
  $ grep -q "module argument does not establish this view's postcondition" incorrect.out
  $ grep -qi 'timeout' incorrect.out
  [1]

A weaker exported view does not replace the implementation's stronger contract.

  $ sed 's/let keep (x : int) = x/let keep (x : int) = x + 1/' checked_exports.ml > incorrect_implementation.ml
  $ cp checked_exports.mli incorrect_implementation.mli
  $ caravan --shh incorrect_implementation.ml > implementation.out 2>&1
  [1]
  $ grep -q 'Verification Error: A postcondition may not hold' implementation.out
  $ grep -qi 'timeout' implementation.out
  [1]
