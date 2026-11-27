Pure parameter operations have one stable logical value, and concrete argument
implementations are checked against their contracts.

  $ caravan --shh positive.ml
  Verification successful.

Pure operations remain usable when surrounding code tracks mutex ownership,
including when one native function is used through ordinary and pure views in
either declaration order.

  $ caravan --shh context.ml
  Verification successful.

An incorrect equality implementation violates the requested interface.

  $ sed 's/let equal (x : int) y = x = y/let equal (x : int) (y : int) = false/' positive.ml > wrong_equal.ml
  $ cp positive.mlp wrong_equal.mlp
  $ caravan --shh wrong_equal.ml > wrong_equal.out 2>&1
  [1]
  $ grep -q "module argument does not establish this view's postcondition" wrong_equal.out

Negative hashes also violate the interface.

  $ sed 's/let hash (x : int) = if x >= 0 then x else 0/let hash (x : int) = -1/' positive.ml > wrong_hash.ml
  $ cp positive.mlp wrong_hash.mlp
  $ caravan --shh wrong_hash.ml > wrong_hash.out 2>&1
  [1]
  $ grep -q "module argument does not establish this view's postcondition" wrong_hash.out

A mutable-state read cannot implement a pure operation.

  $ caravan --shh stateful.ml > stateful.out 2>&1
  [1]
  $ grep -q 'Unsupported Error:' stateful.out

Pure contracts cannot require heap resources.

  $ caravan --shh resourceful.ml > resourceful.out 2>&1
  [1]
  $ grep -q 'pure library function whose contract depends on heap resources' resourceful.out

The pure model's range facts require an admissible key, even though the model
has a total extension over the entire logical carrier.

  $ caravan --shh domain.ml > domain.out 2>&1
  [1]
  $ grep -q 'Verification Error: A postcondition may not hold' domain.out

An ordinary formal contract cannot be strengthened to a pure operation without
an implementation establishing purity.

  $ caravan --shh ordinary.ml > ordinary.out 2>&1
  [1]
  $ grep -q 'A pure module operation requires a pure implementation contract' ordinary.out
