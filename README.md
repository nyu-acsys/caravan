<p align="center">
  <img width="100%" src=".github/assets/banner.png" alt="Caravan: Verification for Multicore OCaml"/>
</p>

<p align="center">
  <a href="https://raw.githubusercontent.com/nyu-acsys/caravan/main/LICENSE"><img alt="MIT licensed" src="https://img.shields.io/badge/license-MIT-blue.svg"/></a>
  <a href="https://github.com/nyu-acsys/caravan/actions/workflows/ci.yml"><img alt="Builds, tests &amp; co" src="https://github.com/nyu-acsys/caravan/actions/workflows/ci.yml/badge.svg?branch=main"/></a>
</p>

Caravan verifies multicore OCaml programs. It translates OCaml 5 code, with
specifications written in comments, to [Raven](https://github.com/nyu-acsys/raven), an
SMT-based verifier for concurrent separation logic, and reports what Raven finds in terms
of the OCaml source.

Caravan is at an early stage of development: so far, it verifies first-order functions on integers, booleans, tuples, lists, options, variant types, mutable records, references and atomics, with loops, predicates and logically atomic contracts. Specifications go in `(*@ ... *)` comments in the `.ml` or its `.mli`, and predicate definitions in the `.ml` or a `.proof` file next to it.

Proof files also support checked lemmas and monomorphic logical variant types.
A lemma has typed parameters and an expression body after `=`. Optional
`returns`, `requires`, and `ensures` clauses state its contract explicitly.
Recursive lemmas require a `variant`, which can be a list for structural
induction. Bindings in the body are immutable and lexical:
`let (value : int) = expression in body`.
Write each clause with its full expression in parentheses, for example
`requires (p x)`, `ensures (result = x)`, and `variant (xs)`.
The final expression supplies the result, or a tuple for multiple `returns`
parameters; a lemma without results ends in a unit expression such as `()`.
Bodies can call other lemmas, use `if` and `match`, and check `assert` expressions.
As in OCaml, `assert false` can finish an unreachable branch of any result type;
the assertion must still be proved. All lemma bodies are verified.

An annotation `(*@ lemma lemma_name args *)` calls a checked lemma from
program code. In a proof body, `unfold p x {n}` names an existential to bind
with `let value = ... in`, and `fold p x {n = value}` supplies its
witness. Unfold bindings infer their types from the named existential declarations;
explicit type annotations remain optional. Use `fold p x` when no explicit witness
is needed.

Specification types include `'a finset`, `'a set`, and `('k, 'v) map` when those
names are not already declared by the program. `Finset` and `Set` provide
`empty`, `singleton`, `mem`, `union`, `inter`, `diff`, and `subset`; `Finset`
also provides `choose`, whose set must be nonempty. Maps use `Map.const`,
`Map.get`, and `Map.set`. A constant map may need an explicit type annotation,
such as `(Map.const 0 : (int, int) map)`.

Proof files can define nonrecursive pure logical functions with typed parameters
and results. A set comprehension uses an OCaml-style binder:

```ocaml
let single (value : int) : int set =
  Set.of_predicate (fun (candidate : int) -> candidate = value)
```

Logical definitions can call previously declared logical functions and use
`let`, `if`, and `match`; they cannot read heap ownership or call predicates.
OCaml checks their bodies and arguments before translation, including reference
element types. Matches must be exhaustive.

Named instances of `SetRA` and `Auth` expose Raven's resource algebras:

```ocaml
type fact = Seen of int
module Facts = SetRA (struct type t = fact end)
module Authority = Auth (Facts)

let facts : (int Atomic.t, Authority.t) Ghost.field = Ghost.field ()
```

Each instance has a distinct resource type. Resource operations are qualified,
such as `Facts.set`, `Authority.auth`, `Authority.frag`, `Authority.auth_frag`,
and `Authority.full`. These declarations support these library instances;
arbitrary module definitions are not supported yet.

`Ghost.at facts cell` names a ghost location attached to an owner of the declared
type. Use it through `own`, for example
`own (Ghost.at facts cell) (Authority.auth (Facts.set known))`.
Declaring a field grants no ownership and performs no allocation. In a lemma
body, `Ghost.fpu location before after` checks a frame-preserving resource update,
consuming ownership of `before` and producing ownership of `after`. It must preserve
compatibility with resources held by other threads. Resource fields do not support
ordinary assignment.

Ghost fields can also store ordinary values, such as `int list` or `bool`.
Ownership defaults to a full share; write
`own ~fraction:Permission.half (Ghost.at contents cell) values` for half ownership.
`Permission.full` names a full share. In checked proof bodies,
`Ghost.read (Ghost.at contents cell)` requires a positive share, and
`Ghost.write (Ghost.at contents cell) values` requires full ownership.
Resource fields use `Ghost.fpu` instead of these reads and writes.

Initialize explicit ghost fields on fresh concrete allocations:

```ocaml
let cell = Atomic.make 0
(*@ initializes [
  Ghost.init contents [];
  Ghost.init facts (Authority.full (Facts.set Set.empty))
] *)
in
cell
```

Each descriptor's owner type must match the allocated reference, and its value
must have the declared field type. Initializers belong to the same allocation as
the concrete fields; they cannot attach to an existing reference or a call to a
constructor function. The supported allocation sites are `ref`, `Atomic.make`,
`Atomic.make_contended`, and fresh mutable records. A field can occur only once
in the initializer list. Explicit fields are independent of generated state,
histories, and action proofs.

Checked proof bodies can allocate a fresh opaque `Ghost.t` reference using
`Ghost.alloc [Ghost.init linked false; Ghost.init retired false]`, where both
field descriptors have owner type `Ghost.t`. These allocations and all ghost
storage operations are erased from the OCaml program. Field reads and
allocations are proof operations; pure logical definitions cannot perform them.
`Ghost` and `Permission` are reserved module names.

Direct invariants use the same declaration syntax as state-based invariants:

```ocaml
invariant live (cell : int Atomic.t) =
  exists value : int. own cell value
```

When the final parameter names a ghost state record declared in the proof, Caravan
elaborates the existing state-based form with its generated support. Otherwise,
all parameters are invariant inputs and the body is emitted directly, without
state, history, or action synthesis.

A `(*@ manual *)` annotation after a function selects a checked manual proof.
The function keeps its OCaml implementation and contract; its proof supplies
invariant opening and closing. Local functions inherit the enclosing manual
mode. A `(*@ proof ... *)` block uses the same expression language as checked
lemmas, including lexical bindings and fold/unfold witnesses. Block-local names
do not escape into the runtime program.

An access annotation attaches a proof closure to one `Atomic` operation:

```ocaml
let read (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun step ->
  let state = unfold live cell {value} in
  let observed = step () in
  fold live cell {value = state};
  observed)
*)
(*@ manual *)
(*@ result = read cell requires live cell ensures live cell *)
```

The operation and result names are freely chosen lexical bindings. Ghost values
bound before the operation remain in scope afterward. The closure must contain
one unconditional `let` binding of the supplied operation applied to `()`, and
end with that binding's unchanged result. Preparation and restoration use
checked ghost expressions. The operation cannot escape, be duplicated, or run
conditionally. Nested accesses have their own annotations; original arguments
are evaluated before their access proof in OCaml order.

Manual and automatic proofs share runtime translation, primitive implementations,
and ghost-expression lowering. Raven checks permissions, invariant closure,
atomicity, and contracts; Caravan checks the annotation shape that preserves the
runtime operation. Manual mode supplies its own invariant proof steps and rejects
automatic `commit`, `returning`, and `performs` annotations.

Manual atomic proofs declare a typed facade in the companion `.proof` file:

```ocaml
module Read = Ghost.AU (struct let operation = read end)
```

`Read.token` identifies updates for that procedure. In a proof expression,
`Read.bind ()` returns the current call's token; repeated binds return the same
value. `Read.access token cell` opens the atomic precondition and returns its
implicit parameters, with inferred types. Multiple implicit parameters form a tuple
in name order. `Read.abort token cell` restores the
precondition; `Read.commit token cell result` establishes the atomic postcondition.
Each operation takes the procedure's concrete arguments in their declared order,
including unit arguments. A unit result is passed as `()`.

For example, with `contents cell value` defined as `own cell value`:

```ocaml
let read (cell : int Atomic.t) = Atomic.get cell
(*@ Ghost.scope (fun step ->
  let token = Read.bind () in
  let value = Read.access token cell in
  unfold contents cell value;
  let observed = step () in
  fold contents cell value;
  Read.commit token cell observed;
  observed)
*)
(*@ manual *)
(*@ result = atomic read cell
    atomic requires contents cell value
    atomic ensures contents cell value && result = value *)
```

`Read.pending token cell` and `Read.committed token cell result` describe the
corresponding AU resources in predicates and lemma contracts. Tokens can be stored
in ordinary ghost fields and passed to checked lemmas, allowing a helper to open
and commit a registered operation. Raven checks the resource and atomicity rules;
Caravan preserves the procedure-specific token types before translation.
AU facades currently name procedures in the same implementation without explicit
ghost parameters. Ghost argument/result transport at runtime calls and specialized
CAS proofs remain subsequent extensions.

## Building

Caravan needs OCaml 5.5 and the library `raven-ivl.api` of Raven, which is not on opam yet.
Install it from Raven's `dev` branch:

```
$ opam switch create caravan 5.5.0
$ eval $(opam env)
$ opam pin add raven-ivl git+https://github.com/nyu-acsys/raven.git#dev
$ opam install . --deps-only --with-test
$ dune build; dune runtest
```

To build against a checkout of Raven instead, link it as `vendor/raven`:

```
$ ln -s ../../raven vendor/raven
```

Raven runs [Z3](https://github.com/Z3Prover/z3) (>= 4.13.0), which has to be on the path.
