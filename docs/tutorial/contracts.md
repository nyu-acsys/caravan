# 2. Contracts and ownership

## Function contracts and heap ownership {#sec:function-contracts-and-heap-ownership}

Caravan's specification syntax is loosely inspired by
[Gospel](https://github.com/ocaml-gospel/gospel). It extends and modifies that
syntax to support separation logic and concurrency reasoning.

Start with a function and its contract from
[`contracts.ml`](../examples/contracts.ml):

```caravan
<!--@include: ../examples/contracts.ml{1,4}-->
```

The contract follows the function in a `(*@ ... *)` comment. It names the function's
arguments and its result. `requires` states what callers must establish; `ensures`
states what the implementation must return. `===` is pure logical equality: it
compares immutable structure recursively and heap references by identity, without
reading their mutable contents. `=/=` is its negation.
The upper bound ensures the executable addition cannot overflow, while the
postcondition uses mathematical arithmetic. Removing the precondition makes the
proof fail at the addition; see [integer semantics](./semantics#sec:integers).

The next function in the same file updates an ordinary OCaml reference:

```caravan
<!--@include: ../examples/contracts.ml{6,12}-->
```

`own cell.contents value` grants ownership of the reference's contents field and
names its initial value. The postcondition returns that ownership with the
incremented value. `value` in the contract is a ghost value, not another runtime
argument. A function returning `unit` can omit the result binding in its contract,
as `increment_cell` does here.

Resource conjunction uses `&&` in specifications: owning both resources requires
compatible permissions. Unmentioned resources held by the caller are preserved by
the separation-logic frame rule. Reading a field requires a positive fractional
share; writing requires full ownership.

This ownership requirement is why specifications distinguish `===` from OCaml's
structural `=`. Comparing references with `=` can read their contents, which another
thread might be changing. Those reads need ownership just like explicit reads.
Specification equality should be pure, so `===` compares the references' identities
instead. This also applies to references nested inside lists, tuples, and other
immutable values. To compare contents, first read them with the required ownership,
then compare the returned values. See
[equality and physical identity](./semantics#sec:equality-and-physical-identity)
for the supported uses of each operator.

Run `caravan contracts.ml`, or save the file in VS Code with the Caravan extension.
Atomics use `own cell value` rather than `own cell.contents value`, as the next
chapter demonstrates. Ordinary reference and record accesses remain non-atomic:
putting a location in a shared invariant does not make an ordinary read safe.

## Separate the implementation from its proof {#sec:separate-the-implementation-from-its-proof}

Caravan reads three sibling files together:

| File | Role |
| --- | --- |
| `example.ml` | Executable OCaml, optionally with inline annotations. |
| `example.mli` | Public OCaml interface and contracts visible to clients. |
| `example.proof` | Predicates, invariants, lemmas, ghost declarations, and proof outlines. |

For a small example, keep the implementation free of annotations in
[`proof_syntax.ml`](../examples/proof_syntax.ml):

<<< ../examples/proof_syntax.ml{caravan}

Describe its exported resource and contract in
[`proof_syntax.mli`](../examples/proof_syntax.mli):

<<< ../examples/proof_syntax.mli{caravan}

The interface declares `stored` without revealing its definition. Callers receive
`stored cell value` when `make value` returns. The implementation proof defines
that predicate and establishes it at the return point:

```proof
<!--@include: ../examples/proof_syntax.proof{1,4}-->
```

These declarations go directly in
[`proof_syntax.proof`](../examples/proof_syntax.proof), without annotation comments.
The predicate body says what `stored` owns. `fold` packages the freshly allocated
field's ownership into that predicate. `proof make = on return ...` attaches this
step to the constructor's return, without changing its runtime body.

Run `caravan proof_syntax.ml` to check the implementation, interface, and proof
together. The remaining examples on this page belong to that same `.proof` file
and are checked as part of the run.

The `.mli` and `.proof` are optional. When an interface exists, Caravan uses
OCaml's signature-inclusion checker to check the implementation against it.
Private functions are also verified unless explicitly marked `trusted`.

Outlines can also select an access with `at (expression)`, as in the next chapter.
Matching ignores formatting and parentheses; ambiguous matches are rejected.
Outlines for local helpers nest inside the enclosing function's outline, and
source modules have corresponding `module ... = struct ... end` proof blocks.
Alternatively, proof annotations can follow their expressions in the `.ml`.
Both forms use the same verifier; a companion proof is not an unchecked assumption.

## Logical code and reusable facts {#sec:logical-code-and-reusable-facts}

A proof file can define pure logical functions using OCaml-style expressions.
This function computes a list's length as an unbounded mathematical `integer`:

```proof
<!--@include: ../examples/proof_syntax.proof{6,10}-->
```

`variant values` gives the decreasing measure for recursion: each call uses the
list's tail. The function exists only in specifications and proofs. It is not a
new executable OCaml function.

A lemma states and proves a reusable fact about that function:

```proof
<!--@include: ../examples/proof_syntax.proof{12,17}-->
```

A lemma has typed parameters, contract clauses, and an expression body after `=`.
Here the empty-list case is immediate. In the other case, the recursive lemma call
supplies the fact about the tail. Raven checks both the postcondition and the
variant decrease. Runtime recursion does not thereby acquire a termination proof.
Lemma bodies can also use `let`, `if`, `assert`, and other lemma calls.

Trailing parameters marked `[@implicit]` may be inferred from owned resources.
This applies to ordinary predicates and to lemma parameters:

```proof
<!--@include: ../examples/proof_syntax.proof{19,30}-->
```

The call `retain cell` infers `value = 7` from the owned predicate. Writing
`retain cell 7` supplies it explicitly. Similarly, `remembered cell` omits the
predicate's implicit value argument. Supply explicit arguments when inference
cannot recover them.

Existential values hidden inside a predicate can be exposed and named with
`unfold`, then supplied to `fold` as named witnesses:

```proof
<!--@include: ../examples/proof_syntax.proof{32,39}-->
```

`{value}` selects the existential to bind as `observed`; its type is inferred.
`{value = observed}` supplies that witness when restoring the predicate. No
runtime field is read or written by these proof steps. When inference suffices,
`fold some_value cell` can omit the witness record.

Logical collections use types such as `'a finset` and `'a sequence`, with
operations available only in specifications and proofs:

```proof
<!--@include: ../examples/proof_syntax.proof{41,43}-->
```

`Finset.singleton` creates a singleton set. `to_sequence` converts a list
to a mathematical sequence while preserving order and length. Logical collections
also include `'a set` and `('k, 'v) map`; use `integer` for unbounded indices.

More elaborate proofs can use resource-algebra modules, ghost fields, and
frame-preserving updates. The
[Raven tutorial](https://nyu-acsys.github.io/raven/tutorial/) explains those proof
techniques; the [segment queue proof](https://github.com/nyu-acsys/caravan/tree/main/test/saturn/michael_scott_queue_lseg)
shows their Caravan syntax in a complete example.

Continue with [concurrent proofs](./concurrent-proofs).
