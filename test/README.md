# Tests

| Directory | Purpose |
| --- | --- |
| `core` | Unit tests for the translator's internal machinery. |
| `spec` | Specification parser tests. |
| `cli` | Command-line behavior tests. |
| `translate` | Focused translation and diagnostic regressions. |
| `examples` | Verified clients, proof patterns, and small algorithm fragments. |
| `saturn` | Saturn implementations and clients, aiming for upstream fidelity modulo annotations. |
| `case_studies` | Substantial independent data structure implementations and their proofs. |

Keep positive and negative checks alongside the sources they exercise. Examples
and case studies should have a directory of their own; focused regressions can
share a directory by feature.

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
