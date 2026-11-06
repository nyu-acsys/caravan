---
layout: home

hero:
  name: Caravan
  text: Verification for multicore OCaml
  tagline: An SMT-based verifier using concurrent separation logic to modularly check functional correctness of multicore OCaml programs.
  image:
    src: /logo.png
    alt: Caravan
  actions:
    - theme: brand
      text: Tutorial
      link: /tutorial/
    - theme: alt
      text: Verified examples
      link: https://github.com/nyu-acsys/caravan/tree/main/test/saturn
    - theme: alt
      text: GitHub
      link: https://github.com/nyu-acsys/caravan

features:
  - title: Reason about concurrency
    details: Ownership, shared invariants, resource algebras, and logically atomic contracts support modular proofs of linearizability for fine-grained concurrent data structures and functional correctness of their clients.
  - title: Work with OCaml programs
    details: Specifications are comments in OCaml source and interfaces. Caravan uses the OCaml compiler's typed program and translates the proof to Raven.
  - title: Keep proofs alongside code
    details: Place contracts in interfaces and detailed ghost proofs in companion files, while preserving the executable OCaml implementation.
  - title: Develop proofs in the editor
    details: The VS Code extension displays source diagnostics, contracts, proof annotations, and streamed verification statuses, and reuses successful proof results.
---

## What Caravan checks

Caravan verifies multicore OCaml programs by translating annotated code to
[Raven](https://nyu-acsys.github.io/raven/), an SMT-based concurrency verifier
founded on concurrent separation logic. Z3 discharges the resulting proof
obligations, and Caravan maps diagnostics back to the OCaml source.

Ownership contracts describe which resources a function needs and returns.
Shared invariants describe resources accessed by multiple threads. Logically
atomic contracts connect implementation proofs to linearizability: each completed
operation takes effect as one abstract step between its invocation and return,
even when its implementation uses several atomic accesses and retry loops.
Clients can use these contracts to prove functional correctness without reasoning
about the operation's internal interleavings.

## Proofs with an OCaml shape

Write specifications in `(*@ ... *)` comments. Function contracts may live next
to an implementation or in its `.mli` interface. A companion `.proof` file can
contain predicates, invariants, lemmas, and proof steps attached to the code.
The OCaml compiler continues to see ordinary OCaml source.

Caravan supports both automatic invariant and history reasoning and explicit
manual proof annotations. The [VS Code extension](https://github.com/nyu-acsys/caravan/blob/main/vs-code/MARKETPLACE.md)
shows external contracts and proof steps in the implementation, with links to
their source files and a read-only combined proof view.

## Verified case studies

The repository includes case studies adapted from
[Saturn](https://github.com/ocaml-multicore/saturn), a library of concurrent OCaml
data structures:

- A [Treiber stack](https://github.com/nyu-acsys/caravan/tree/main/test/saturn/treiber_stack)
  and [stack-drain clients](https://github.com/nyu-acsys/caravan/tree/main/test/saturn/stack_drain).
- A [Michael–Scott queue with a history-based proof](https://github.com/nyu-acsys/caravan/tree/main/test/saturn/michael_scott_queue).
- The same queue with an [explicit segment-based proof](https://github.com/nyu-acsys/caravan/tree/main/test/saturn/michael_scott_queue_lseg).

These examples include polymorphic implementations, contracts, proof annotations,
and clients. They also serve as verification regressions.

## Project status

Caravan is under active development. It supports a growing first-order subset of
OCaml, including polymorphic functions, algebraic data types, records, modules and
functors, mutable state, atomics, exceptions, and constant GADT witnesses. It does not yet
cover the full OCaml language. The [OCaml coverage guide](/tutorial/ocaml-subset)
describes the supported constructs and current restrictions.

The [Caravan tutorial](/tutorial/) starts with a first verified file, then
introduces contracts and both proof modes. For the underlying logic,
the [Raven tutorial](https://nyu-acsys.github.io/raven/tutorial/) introduces
ownership, invariants, and atomic contracts through worked examples.

Caravan is developed in the [ACSys group](https://cs.nyu.edu/acsys) at New York
University and is available under the MIT license.
