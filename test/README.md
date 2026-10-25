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
