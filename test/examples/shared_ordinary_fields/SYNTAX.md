# Field discipline annotations

Native field attributes declare the discipline of an ordinary mutable field:

```ocaml
type node = {
  mutable counter : int [@caravan.frozen];
  mutable capacity : int [@caravan.relaxed];
}
```

The same attributes work on fields of inline constructor records and in
signatures. The `caravan.` prefix follows the convention for native OCaml
attributes such as `[@@caravan.local]`; specification attributes such as
`[@grows]` are unprefixed.

A companion proof can name the attributed fields with selector façades:

```ocaml
module Counter = Ghost.Frozen (struct
  let field (n : node) = n.counter
end)

module Capacity = Ghost.Relaxed (struct
  let field (n : node) = n.capacity
end)
```

A constructor pattern selects fields of an inline constructor record, as in
Saturn's bounded queue:

```ocaml
module Counter = Ghost.Frozen (struct
  let field (Node r : (_, [< `Node]) node) = r.counter
end)
```

OCaml's type checker resolves the field and infers the stored value's type.
The selector must directly project a mutable ordinary field from its bound
receiver. The façade must match the declaration's attribute. Compatible aliases
can name the same field; a façade cannot assign a mode to an unannotated field.

Attributes enable the hidden execution context and cumulative atomic release
metadata. Frozen fields support source allocation, full-permission writes and
private reads by the last writer. One record allocation initializes its payload
and metadata slots together. Plain `own n.counter value` existentially hides the
last writer, and fractional ownership covers all three slots. A source write
establishes the executing owner's writer identity before a private read.
Contracts can preserve the last writer explicitly:

```ocaml
type cell = { mutable counter : int [@caravan.frozen] }

let allocate value = { counter = value }
(*@ n = allocate value
    ensures own ~writer:Ghost.self n.counter value *)

let read n = n.counter
(*@ result = read n
    requires own ~writer:Ghost.self n.counter value
    ensures own ~writer:Ghost.self n.counter value && result === value *)
```

`Ghost.self` denotes the executing domain's hidden identity in procedure
contracts and attached proof scopes. An explicit writer must have type `Ghost.t`.
The writer label composes with `~fraction` in either order. Global predicates
and lemmas take an explicit writer parameter, for example:

```ocaml
predicate owned_by (n : cell) (value : int) (writer : Ghost.t) =
  own ~writer:writer n.counter value
```

Plain ownership hides the writer and cannot establish current-writer evidence.
A full-permission source write establishes that evidence even for a same-value
write. `~writer` is supported only for Frozen fields.

For the cell above, declare its façade in the companion proof:

```ocaml
module Counter = Ghost.Frozen (struct
  let field (cell : cell) = cell.counter
end)
```

A Frozen façade exposes the proof step `Counter.freeze n` and the persistent
resource `Counter.frozen n value`. The step consumes full current-writer
ownership. For example, a manual scope attached to a checked allocator call can
seal the newly allocated field:

```ocaml
let create value = allocate value
(*@ Ghost.scope (fun step ->
    let cell = step () in
    Counter.freeze cell;
    cell) *)
(*@ manual *)
(*@ result = create value ensures Counter.frozen result value *)
```

The frozen resource hides the backend cut, can be duplicated, and fixes both
the field identity and its value. A freeze records its cut in the executing
context. A domain-indexed visibility resource permits exact reads:

```ocaml
let read (cell : cell) = cell.counter
(*@ Ghost.frozen_scope (fun load ->
    let result = load () in
    result) *)
(*@ manual *)
(*@ result = read cell
    requires Counter.visible Ghost.self cell value
    ensures Counter.visible Ghost.self cell value && result === value *)
```

`Counter.visible owner cell value` combines the frozen fact with evidence that
`owner` has acquired its cut. A constructor may return
`Counter.visible Ghost.self result value` after freezing its own field. Contracts
and proof predicates can pass an explicit `Ghost.t` owner. A frozen fact alone,
or visibility evidence for another owner, does not authorize the read.

`Ghost.frozen_scope` uses the existing checked scope wrapper and selects the
non-atomic frozen-read contract. Unannotated reads keep the private-read
contract. The distinction keeps private procedures free of a requirement to
open the frozen invariant. The wrapper must attach to an ordinary Frozen field
read in a manual proof. `Ghost.State.frozen_scope` provides the same selection
with lexical proof state. Cross-domain publication contracts and the Relaxed
source bridge remain pending.
Defining signatures can supply disciplines to fresh fields. Caravan checks
established disciplines at supported ascriptions and functor applications.
Manifest record re-exports inherit the discipline of the original field.
The handwritten Raven models in this directory remain separate experiments.

`Capacity.observe read` inside a `Ghost.scope` continuation remains proposed.
Source atomic operations carry publication/acquisition metadata. Exposing their
cut lower bounds in source contracts, and propagation through Domain
synchronization, remain pending.
Observation evidence will certify a recorded origin, rather than the latest
value or ownership of a payload.
