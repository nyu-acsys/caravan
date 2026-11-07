<p align="center">
  <img width="100%" src=".github/assets/banner.png" alt="Caravan: Verification for Multicore OCaml"/>
</p>

<p align="center">
  <a href="https://raw.githubusercontent.com/nyu-acsys/caravan/main/LICENSE"><img alt="MIT licensed" src="https://img.shields.io/badge/license-MIT-blue.svg"/></a>
  <a href="https://nyu-acsys.github.io/caravan/"><img alt="Project documentation" src="https://img.shields.io/badge/docs-nyu--acsys.github.io%2Fcaravan-blue.svg"/></a>
  <a href="https://github.com/nyu-acsys/caravan/actions/workflows/ci.yml"><img alt="ci" src="https://github.com/nyu-acsys/caravan/actions/workflows/ci.yml/badge.svg"/></a>
</p>

Caravan is an SMT-based verifier for multicore OCaml programs. It uses concurrent
separation logic to check functional correctness, including modular proofs of
linearizability through logically atomic contracts. Caravan translates annotated
OCaml to [Raven](https://github.com/nyu-acsys/raven) and reports verification results
at the OCaml source.

Specifications are comments in `.ml` or `.mli` files. Detailed proofs can live in
companion `.proof` files, keeping the executable code unchanged. Caravan supports
both automatic invariant reasoning and explicit ghost proofs.
Its specification syntax is loosely inspired by
[Gospel](https://github.com/ocaml-gospel/gospel), extending and modifying it to
support separation logic and concurrency reasoning.

```ocaml
let increment value = value + 1
(*@ result = increment value
    requires value < max_int
    ensures result === value + 1 *)
```

Caravan is under active development. It supports a first-order subset of OCaml 5,
including polymorphic functions, algebraic data types, records, modules and
functors, mutable state, atomics, exceptions, and constant GADT witnesses.
See the [tutorial](https://nyu-acsys.github.io/caravan/tutorial/) for examples,
[language coverage](https://nyu-acsys.github.io/caravan/tutorial/ocaml-subset), and
[semantic conventions](https://nyu-acsys.github.io/caravan/tutorial/semantics).

## Getting started

The [VS Code extension](vs-code/MARKETPLACE.md) bundles Caravan, its linked Raven
verifier, Z3, and matching OCaml interfaces for Linux x64, macOS arm64, and Windows
x64. It works alongside OCaml Platform, showing diagnostics, contract hovers,
proof hints, and streamed verification statuses.

With Caravan installed, verify a file from the command line:

```bash
caravan example.ml
```

The [tutorial](https://nyu-acsys.github.io/caravan/tutorial/) covers installation,
a first check, annotations, and both proof modes. The
[Raven tutorial](https://nyu-acsys.github.io/raven/tutorial/) introduces the
underlying separation logic.

## Examples

The [Saturn case studies](test/saturn) include:

- A [polymorphic Treiber stack](test/saturn/treiber_stack) and
  [stack-drain clients](test/saturn/stack_drain).
- A [Michael–Scott queue with automatic history reasoning](test/saturn/michael_scott_queue).
- The same queue with an [explicit segment proof](test/saturn/michael_scott_queue_lseg).

Smaller [verification examples](test/examples) illustrate individual proof patterns.
See [test organization](test/README.md) for the full collection.

## Building

Caravan requires OCaml 5.5 and Raven's `raven-ivl.api` library. From a source checkout:

```bash
opam switch create caravan 5.5.0
eval $(opam env --switch=caravan)
opam pin add raven-ivl.1.6.1 "git+https://github.com/nyu-acsys/raven.git#$(cat RAVEN_REVISION)"
opam install . --deps-only --with-test
dune build
```

[Z3](https://github.com/Z3Prover/z3) version 4.13.0 or later must be on `PATH`.
Run `dune exec -- caravan example.ml` to use the local build.
The [build guide](https://nyu-acsys.github.io/caravan/tutorial/#sec:build-from-source)
also describes using a sibling Raven checkout.

Run the regression tests with `dune runtest -j2` and check formatting with
`dune build @fmt -j2`. See [extension development](vs-code/README.md) and
[site development](docs/README.md) for their separate build instructions.
