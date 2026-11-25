Concrete generic heap layouts and invariant aliases survive an opaque export
boundary, including repeated applicative instances.

  $ caravan --shh checked_export_heap.ml
  Verification successful.

An opaque export cannot silently inherit additional private invariant namespaces.

  $ cp checked_export_heap.ml private_namespace.ml
  $ cp checked_export_heap.mli private_namespace.mli
  $ sed 's/invariant stored (cell : t) = true/invariant hidden (cell : t) = true\n  invariant stored (cell : t) = hidden cell/' checked_export_heap.proof > private_namespace.proof
  $ caravan --shh private_namespace.ml > private.out 2>&1
  [1]
  $ grep -q 'invariant native_hidden required by' private.out
  $ grep -q 'not available in the current mask' private.out
  $ grep -qi 'timeout' private.out
  [1]

An exported invariant must retain the actual resource kind.

  $ cp checked_export_heap.ml incorrect_resource.ml
  $ cp checked_export_heap.proof incorrect_resource.proof
  $ sed '/^module Instance/,/^end/ s/invariant stored/predicate stored/' checked_export_heap.mli > incorrect_resource.mli
  $ caravan --shh incorrect_resource.ml > resource.out 2>&1
  [1]
  $ grep -q 'resource declaration stored has a different kind or arity' resource.out
