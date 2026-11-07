# 5. Semantics and verification limits

A proof establishes properties of Caravan's runtime model under the function's
precondition and its dependency contracts. The following distinctions matter when
reading those properties as claims about OCaml programs.

## Integers {#sec:integers}

Runtime `int` values have OCaml machine bounds. Ordinary executable arithmetic
must not overflow: Caravan generates obligations for operations such as `+`, `-`,
`*`, division, and unary negation. Division also requires a nonzero divisor.
OCaml itself can wrap on overflow; Caravan currently rejects such ordinary
arithmetic rather than using wraparound to prove its contract.

Specification arithmetic is mathematical. In `ensures result === value + 1`, the
addition does not wrap. Quantifiers over `int` range over bounded source integers;
the specification-only type `integer` ranges over all mathematical integers.
Logical datatypes and mathematical collections are not automatically restricted
to runtime-representable values just because a field has type `int`. At boundaries
back to executable code, source-value constraints must hold.

The atomic arithmetic operations `Atomic.fetch_and_add`, `Atomic.incr`, and
`Atomic.decr` are modeled with wrapping behavior. Do not transfer a no-overflow
fact from ordinary addition to these operations.

## Equality and physical identity {#sec:equality-and-physical-identity}

| Operators | Interpretation |
| --- | --- |
| `=`, `<>` | OCaml structural comparison on supported runtime values; mathematical equality on logical values. |
| `==`, `!=` | Physical equality/inequality in code; exact for heap references and immediate values, conservative for boxed immutable values. Boxed physical comparison is rejected in specifications. |
| `===`, `=/=` | Specification-only logical equality/inequality: compare immutable structure recursively and heap references by identity, without reading their contents. |

`===` and `=/=` map directly to Raven's equality and inequality. They are not
OCaml executable operators. For two lists of references, logical equality compares
the list structure and the reference identities, not the referenced contents.
Two different references containing the same integer are logically unequal. For
example, two separately allocated references both containing `7` compare equal
with OCaml's structural `=`, but unequal with `===`. Comparing either reference
with itself using `===` remains true even when its contents change.

The reason for this distinction is ownership: structural equality can traverse
the concurrently mutable heap. Its reads need resource ownership, just like an
explicit dereference. Treating such a comparison as a pure proposition would hide
those reads and the permissions they require. `===` keeps specification equality
pure by comparing heap locations by identity, without observing mutable contents.
It therefore needs no ownership of those contents merely to compare references.

OCaml's structural `=` can dereference mutable data. Caravan rejects it for
runtime types containing references or mutable records, including through tuples,
variants, or lists, in both code and specifications. Tests against nullary
constructors such as `xs = []` remain supported. Use identity to compare references,
and explicit owned reads to compare their contents.

OCaml's physical comparison and `Atomic.compare_and_set` compare boxed immutable
values, such as nonempty lists, by physical identity. Structurally equal values
need not be the same allocation, so structural equality does not guarantee CAS
success in OCaml either.

Caravan's model additionally abstracts away some allocation identity. Its CAS
encoding is a sound overapproximation of OCaml's behavior for the supported value
representation: every concrete CAS outcome is allowed by the model, which may
also admit extra outcomes. For boxed values, success requires logical equality;
when the values are logically equal, the model permits either success or failure.
Success stores the new value, and failure leaves the current value unchanged.

For example, after reading a boxed value from an atomic, Caravan may allow a CAS
using that value to fail even if the atomic has not changed; OCaml's CAS succeeds
in that situation. Conversely, separately allocated but logically equal values
may compare successfully in the model although OCaml distinguishes their physical
identities. These extra behaviors make safety proofs more conservative: a property
proved for all modeled executions also holds for the concrete executions they
represent. The loss of precision can make valid properties harder to prove; it
does not establish progress or allocation-sensitive ABA arguments.

## Memory access and evaluation {#sec:memory-access-and-evaluation}

Ownership makes ordinary reference and mutable-record accesses race-free.
A positive fraction permits reads; full ownership permits writes. These accesses
use non-atomic contracts, so a proof cannot open a shared invariant around an
ordinary access as if it were atomic. Use `Atomic` operations where shared accesses
need atomicity. Caravan relies on OCaml's race-free/atomic execution model; it does
not justify racy ordinary reads or writes by assuming every field access is atomic.

The translator evaluates ordinary application arguments right to left and preserves
short-circuit behavior of `&&` and `||`. OCaml does not promise a general argument
evaluation order at the language level. This is a potential soundness gap relative
to OCaml's language semantics: a proof may rely on Caravan's chosen order even
though another OCaml implementation could evaluate the arguments differently.
Avoid this gap by using explicit `let` bindings to force an order whenever
argument evaluation has interacting effects. An access-proof closure runs after
the attached operation's arguments have been evaluated; it cannot reorder those
runtime effects.

## What successful verification establishes {#sec:what-successful-verification-establishes}

Contracts describe partial correctness, including specified exceptional outcomes.
Verification does not by itself prove runtime termination, lock freedom, wait
freedom, fairness, or resource bounds. A retrying operation can satisfy its
contract without a proof that every call returns. Logical recursive definitions
and lemmas separately require decreasing variants.

Exceptions named by normal and atomic exceptional contracts are part of the proof.
Do not read successful verification as a claim about all environmental failures,
including allocation failure or asynchronous runtime behavior. The verifier also
does not check an unmodeled domain-spawning harness.

Manual ghost proofs are checked, not trusted shortcuts. Their operations erase
from execution, and access scopes must preserve the attached runtime operation.
Automatic and manual modes share primitive semantics; choosing manual mode does
not relax the memory or atomicity rules.

## Trusted code and imports {#sec:trusted-code-and-imports}

The trust boundary includes the OCaml compiler, Caravan's translation and primitive
models, Raven, and the SMT solver. OCaml interface compatibility is checked, but
that establishes types, not imported behavioral contracts.

- A function explicitly annotated `(*@ trusted *)` has its body skipped; callers
  assume its contract, even when it is defined in the file being checked.
- Imported `.mli` contracts are assumed when checking clients. Verify their
  implementations separately against those same contracts. Importing a contract
  never verifies its implementation or loads its private proof as an assumption.
- Bundled standard-library behavioral contracts are trusted. Their mathematical
  models and auxiliary lemmas are checked by `caravan --check-stdlib` and by the
  regression suite.
- An imported `pure` operation promises purity, determinism, and termination when
  its precondition holds, as well as its contract. A specification call denotes a
  total mathematical extension; outside the precondition or source domain its
  result is unconstrained. Runtime calls must establish the precondition.
- `[@@caravan.local]` on an imported operation promises it takes no shared-memory
  steps and invokes no callbacks. It supports contract expansion for opaque allocation
  and persistent facts. This is a trusted library promise, not something inferred
  from the postcondition. `[@@caravan.opens []]` separately restricts which
  invariants an operation may open; verified bodies must respect it.

These assumptions are particularly important for interface stubs used to model
libraries that Caravan cannot yet translate.

## Running and debugging checks {#sec:running-and-debugging-checks}

Run `caravan --help` for the complete command-line interface. Common options are:

| Option | Purpose |
| --- | --- |
| `-I DIR` | Add interface-stub dependencies. |
| `--no-dune` | Disable automatic Dune dependency discovery. |
| `--smt-timeout MS` | Set the timeout per solver query; the default is 10000 ms. |
| `--cache-dir DIR` | Reuse successful checks with unchanged proof dependencies. |
| `--emit-rav` | Inspect the generated Raven program instead of verifying it. |
| `--check-stdlib` | Check bundled mathematical models and lemmas. |

A solver timeout means the obligation was not proved within the budget; it does
not establish a counterexample. Cached results are reused only when Raven's proof
fingerprints match. Parsing, typing, and translation still run to establish the
current obligations.

For editor installation, settings, diagnostic markers, and proof views, see the
[extension user guide](https://github.com/nyu-acsys/caravan/blob/main/vs-code/MARKETPLACE.md).
For larger worked programs, continue with the
[Saturn case studies](https://github.com/nyu-acsys/caravan/tree/main/test/saturn).
