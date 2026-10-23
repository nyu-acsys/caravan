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
ordinary assignment. Allocation and initialization hooks for runtime code are not
available yet.

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
