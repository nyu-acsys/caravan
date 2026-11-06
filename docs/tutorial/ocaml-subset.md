# 4. OCaml coverage

Caravan uses OCaml's typed program, but accepts a subset of OCaml rather than
every type-correct program. Unsupported constructs normally produce a source
error. Existing OCaml libraries also need contracts: being accepted by the OCaml
compiler does not make an arbitrary library call verifiable.

## Expressions, types, and effects {#sec:expressions-types-and-effects}

| Area | Supported | Important restrictions |
| --- | --- | --- |
| Values | `int`, `bool`, `unit`, tuples, lists, options, variants, immutable records. | No general support for strings, floats, arrays, or objects. |
| Control flow | `let`, `if`, pattern matching, sequencing, recursive functions, `while` and `for` loops. | Supply loop invariants when the inferred facts are insufficient; `variant` annotations on executable functions and loops are not yet supported. |
| Functions | Named first-order functions, local helpers and captures, recursion, and rank-one polymorphism. | No general function-valued parameters, returned closures, or callbacks; no independently generalized helper that also depends on enclosing type parameters. |
| Data types | Parameterized variants and immutable records, including regular recursive types and aliases. | Parameterized mutable records, inline constructor records, and nonregular recursive data types are unsupported. |
| Mutable state | References, monomorphic mutable records, and supported `Atomic` operations. | Reads/writes require ownership; ordinary fields are non-atomic. |
| GADTs | Constant witness types, including Saturn's result-selection witnesses. | Not arbitrary GADTs or dependent payloads. |
| Exceptions | Declared exceptions, supported handlers, and normal and exceptional contracts. | Contracts must account for exceptional outcomes; this is not a model of every runtime or system exception. |
| Concurrency | Atomics, shared invariants, logically atomic contracts, explicit ghost resources and helping proofs. | No `Domain.spawn`/`Domain.join` harness or general `Mutex`/`Condition` library support yet. |

Generic functions are checked once with constraints on their type parameters,
rather than by verifying each concrete call separately. Those constraints preserve
source-value admissibility, including integer bounds and domains of nested
containers. Local helpers can capture enclosing values and type parameters.
Ordering on unconstrained generic values and explicitly quantified source type
annotations remain outside the supported subset.

Checked `variant` annotations currently apply to logical functions and lemmas in
`.proof` files. Executable functions and loops are verified for partial correctness,
without proving termination.

Assertions, loop invariants, and contracts carry proof obligations. For an exception
contract, use `raises Exception -> proposition` (or `atomic raises` for an atomic
outcome). A logical `pure` function can be used in specifications when it meets
Caravan's purity and termination requirements; arbitrary OCaml calls cannot be
embedded in a proposition.

## Modules and functors {#sec:modules-and-functors}

Caravan supports ordinary and nested `module ... = struct ... end`, aliases,
named signatures, `.mli` abstraction, and signature `include`. Export contracts in
the signature; callers through an interface use those contracts, not private
implementation definitions. Proof modules mirror source modules and may contain
logical types, predicates, invariants, lemmas, ghost fields, and resource-algebra
instances.

Supported source functors have named module parameters or unit parameters and a
structure body. Ordinary currying and partial application are supported. Argument
signatures may expose polymorphic operations, predicates, and abstract type
constructors such as `type 'a t`. Proofs are shared through Raven functors where
the generic representation supports the body; other supported bodies use separate
verified specializations.

There is currently a verification-coverage gap compared with Raven: Caravan
discovers runtime functor bodies through applications in the input being checked.
An unapplied functor's runtime bodies can therefore be skipped, even if their
contracts are false. This is a limitation of the translation, not the intended
modular verification behavior.

Repeated applicative applications to the same module share result identity;
aliases preserve that identity. Unit applications introduce fresh identities.
These distinctions matter for abstract types, heap fields, and proof resources.
The [stack-drain client](https://github.com/nyu-acsys/caravan/tree/main/test/saturn/stack_drain)
and [functor queue examples](https://github.com/nyu-acsys/caravan/tree/main/test/examples/functor_ms_queue)
show supported module-level reuse.

Important remaining module restrictions include:

- Recursive modules, local modules, and first-class modules. Higher-order and
  imported functors are not supported by the shared generic translation.
- `open`, structure `include`, and module initialization expressions.
- Anonymous functor arguments, nested parameter modules, and parameter-dependent
  heap representations in the generic translation.
- Signature includes containing abstract proof modules; repeated callable
  ascription of already checked module views and polymorphic forwarding through
  those views.
- Raising operations, explicit ghost adaptations, public update tokens, and
  nested members in contract-adapting checked aliases.

Named constrained aliases can check a requested contract against an existing
module. They preserve resource identity while using OCaml's visible type equalities.
This support is narrower than ordinary aliasing; consult the
[module regressions](https://github.com/nyu-acsys/caravan/tree/main/test/translate/modules)
when a proof needs a more elaborate signature adaptation.

## Libraries and dependency discovery {#sec:libraries-and-dependency-discovery}

In Dune projects, Caravan discovers the input file's library or executable and its
transitive local interface dependencies. Dune must be on `PATH`. It imports usable
`.mli` source contracts even when implementations sit alongside them, without
verifying those implementations. Generate missing interfaces beforehand.

Discovery does not reproduce preprocessing or all Dune compiler flags. Multi-module
wrapped libraries remain unsupported. Outside a project, interface-only stubs in
the source directory or `-I` directories provide dependencies. Explicit stubs win
over discovered interfaces with the same module name. Use `--no-dune` for standalone
lookup. A compiled `.cmi` alone is not an annotated contract.

Bundled annotated subsets of the standard library currently include:

| Operations | Model |
| --- | --- |
| `List.rev`, `List.rev_append` | List reversal, usable in implementations and specifications. |
| `Seq.empty`, `List.to_seq`, `List.of_seq` | Finite, reusable snapshots, described by `Seq.persistent sequence values`. |

Snapshots remain usable after the originating data structure changes. User-defined
sequence producers, direct sequence-thunk calls, stateful/one-shot sequences, and
higher-order list operations need further higher-order support. General `lazy`,
effect handlers, `Obj`, and first-class modules are outside the current subset.

The bundled [standard-library interfaces](https://github.com/nyu-acsys/caravan/tree/main/lib/stdlib)
state their precise contracts. Their `.proof` companions supply reusable checked
mathematical models and lemmas; clients do not reprove those facts. `Stdlib_model`
provides their logical models only in specifications. The
[next page](./semantics#sec:trusted-code-and-imports) describes what is trusted.
