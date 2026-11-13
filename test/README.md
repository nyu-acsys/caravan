# Tests

| Directory | Purpose |
| --- | --- |
| `core` | Unit tests for the translator's internal machinery. |
| `spec` | Specification parser tests. |
| `cli` | Command-line behavior tests. |
| `translate` | Focused translation and diagnostic regressions. |
| `examples` | Verified clients, proof patterns, and small algorithm fragments. |
| `saturn` | Saturn implementations and clients, aiming for upstream fidelity modulo annotations. |
| `moonpool` | Moonpool implementations with companion proofs and unchanged upstream source. |
| `ocaml5_tutorial` | OCaml 5 tutorial implementations with companion proofs and checked clients. |
| `case_studies` | Substantial independent data structure implementations and their proofs. |

Keep positive and negative checks alongside the sources they exercise. Examples
and case studies should have a directory of their own; focused regressions can
share a directory by feature.

## Running the suites

Run from the repository root in the project's opam switch:

```bash
dune build @quick -j2       # Representative regression coverage for iteration.
dune runtest -j2            # Comprehensive validation.
dune build @fmt -j2
```

`quick` selects existing test actions through the explicit aliases in
[test/dune](dune). Both suites run the same commands for a selected test, and Dune
shares their results, so running `quick` before `runtest` on an unchanged build
prioritizes these checks without repeating them. `runtest` retains every distinct
check, including all case studies, configurations, mutations, and serialization
checks. Use it for final validation; a quick pass does not cover every combination
in the full suite.
Run one verifier-heavy suite at a time, with at most `-j2`.

The quick suite includes all `core` and `spec` unit tests, plus the following
representative checks. The alias list is the source of truth for individual tests.

| Area | Quick coverage |
| --- | --- |
| Values and storage | Arithmetic and wraparound, equality, patterns, collections, heap ownership, dynamic initialization, and rejected unsupported constructs. |
| Contracts and proofs | Loops, recursion, predicates, implicit parameters, ghost storage, manual scopes, atomic-update commit/abort, and failure diagnostics. |
| Modules | Signatures, includes, imports, aliases, ordinary/unit/curried functors, result types, generic proof reuse, and resource algebras. |
| Polymorphism and GADTs | Functions, records, data types, proof parameters, source-value admissibility, constant witnesses, and constructor-set indices. |
| Concurrency | Atomic permissions, domains, mutexes, condition variables, exceptions, resource transport, and invalid ownership/lifecycle operations. |
| Shared fields | Discipline identity, freezing and owner-indexed reads, publication, relaxed journals, raw-payload validation, atomic visibility, and rejected authority fabrication. |
| Interfaces and tooling | Standard-library models, tutorial examples, CLI output, source locations, editor metadata, and verification-cache invalidation. |
| Integration | The Treiber stack, Moonpool Parker, and module/functor stack clients, including incorrect clients. |

The comprehensive suite additionally exercises the full history and segment queue
proofs, their module/functor variants and mutations, the parallel stack-drain
harness, and the broader combinations of field disciplines and resource transfers.

When adding a feature, include successful verification and a meaningful rejection
case in `quick`. Keep relevant soundness regressions even when they are not the
cheapest tests. Split large scripts into independent groups when a representative
subset suffices for quick feedback; each command should still run only once in the
comprehensive suite unless its second run tests a distinct path, such as standalone
Raven serialization. Review the selection by behavior rather than automatically
selecting tests below a timing threshold.

Implementation proofs are checked by their defining tests. Client tests use the
imported `.mli` contracts and check the client obligations; they do not reverify
the imported implementation. The comprehensive suite checks the implementation
separately. Running a client test alone assumes its imported contracts.

Mutation tests may use `--only` to check the changed source member and its local
helpers, provided a positive test verifies the complete implementation separately.
Keep mutations that exercise global checks or interactions outside that member
unrestricted. Native API protocol tests similarly verify each shared support
configuration once, then use `select_member` to check individual probes against
those contracts. Selection tests cover omitted failures, frontend errors,
attached proofs, nested members, and cache isolation.

For a fresh timing measurement, build first, then time the desired suite:

```bash
dune clean
dune build -j2 --cache=disabled
time dune build @quick -j2 --cache=disabled
```

Disabling the shared cache and cleaning ensures the actions actually execute.
`--force` alone can reuse unchanged cram results with Dune 3.24.2. Ordinary
incremental runs intentionally reuse previous successful results.

## Case-study sources

The Saturn sources and clients also have ordinary Dune library stanzas, so
`dune build` checks their OCaml types and supplies editor configurations to OCaml
Platform. Select the project's OCaml 5.5 switch in the editor and build from the
repository root. Backoff is an interface-only dependency; these stanzas compile
the examples but do not provide an executable Backoff implementation.

The queue interfaces use separate `MS_QUEUE` module types, as Saturn does. The
history queue preserves Saturn's interface text and documentation, with Caravan
annotations inserted beside its declarations. The segment variant exposes its
currently verified subset with a list-valued specification. These interfaces are
excluded from `ocamlformat` to preserve their upstream formatting.

The history queue implementation is the unchanged file from Saturn commit
`50d8d9d0a99b40434ab05bee49200cd5ffa028f5`; its annotations live in the companion
proof and interfaces. The source-parity regression checks its exact bytes and
the original interface bytes after removing inserted annotations. Formatting
excludes this implementation too, and its source files use LF line endings.

Moonpool examples follow the same per-data-structure layout under `moonpool/`.
The Parker implementation retains its upstream bytes, checked by the source-parity
regression, and its annotations live in a companion `.proof` file.
