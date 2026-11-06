# 3. Concurrent proofs

A logically atomic contract describes an operation as one abstract step between
invocation and completion. It supports modular linearizability proofs even when
the implementation performs several accesses and retries. `atomic` in a contract
does not assert that the whole implementation is physically atomic.

For each example below, download its implementation, interface, and proof into
one directory. Invoke Caravan on the `.ml` implementation; it loads the sibling
`.mli` and `.proof` files automatically. Both examples are checked by the
repository's regression suite.

## Actions and linearization points {#sec:actions-and-linearization-points}

A concurrent operation usually takes several concrete steps, while its contract
promises one abstract logical step. An automatic proof connects these two accounts
using a state interpretation, actions, and linearization annotations.

The **state interpretation** is the shared invariant: it describes which concrete
heap resources represent a given proof state. A `view` projects that state into a
resource exposed to clients. The state can include representation details as well
as the abstract value clients observe.

An **action** describes a change to this state. It names the state fields that
change and can associate the change with a concrete atomic operation, such as a
successful CAS. This declaration describes a proof transition; it does not execute
any OCaml code. At an annotated access, Caravan must prove that the actual heap
operation realizes the declared state change and that the invariant can be
restored with the resulting state. Declaring an action does not assume that the
implementation satisfies it.

A **linearization annotation** identifies where an invocation fulfills its atomic
contract. At that point the proof must connect the resources in `atomic requires`
to those in `atomic ensures`, including the promised result. Updating the proof
state and linearizing an invocation are distinct responsibilities: an internal
representation change need not itself complete a public operation, and a read
can linearize without changing the state.

Caravan expresses these responsibilities separately:

| Construct | Role in the automatic proof |
| --- | --- |
| `action` *name* … `~>` … | Describe the state transition, optionally linked to a concrete atomic operation. |
| `performs` *name* at an access | Apply that action at the selected implementation step. For an action tied to CAS, the transition occurs only when the CAS succeeds. |
| `linearizes` *operation* in an action declaration | Specify that performing the action also commits the named operation's atomic contract. |
| `commit` at an access | Commit the current operation's atomic contract without naming a state-changing action, as for a read. |

Consequently, one operation may perform several actions while linearizing only
once. A failed CAS can restore the invariant without changing the state or
committing the operation, allowing a retry. Read-dependent linearization can use
`returning pattern -> commit` to commit only for a selected observed value. These
annotations guide a checked proof; marking a step does not make it a valid
linearization point by itself.

Other threads may change shared state between concrete atomic steps. The proof
therefore reasons from the state available at the selected access, not by assuming
that an earlier read is still current. Before the linearization point, the atomic
update remains pending; at the point, its postcondition must be established; after
that, the implementation must return a result consistent with the committed
outcome. This is how a multi-step implementation can justify a single-step client
contract.

This separation of concrete representation, abstract transitions, and atomic
specifications is closely related to
[TaDA: A Logic for Time and Data Abstraction](https://www.d-y.me.uk/papers/tada.pdf)
(da Rocha Pinto, Dinsdale-Young, and Gardner, ECOOP 2014). TaDA describes shared
regions through state interpretations and transition protocols, with guards
controlling transitions; its atomicity tracking records whether the promised
abstract update has occurred. The
[Voila proof-outline checker](https://doi.org/10.1007/s10703-023-00427-w)
shows how annotations can guide automated checking of TaDA proofs. These are
conceptual connections: Caravan's `action` declarations are its own automation
layer over [Raven's Iris-based logic](https://cs.nyu.edu/~wies/publ/cav25_raven.pdf),
rather than TaDA's full region-and-guard machinery.

## Automatic mode: an atomic cell {#sec:automatic-mode-an-atomic-cell}

We now demonstrate these concepts with a small atomic cell.

An atomic cell stores one value that multiple threads can read and replace safely.
`create value` allocates a cell with an initial value, `read cell` returns its
current value, and `set cell value` replaces it. Here `set` uses a CAS retry loop
to illustrate proving a logically atomic operation with multiple concrete steps.

The implementation is ordinary polymorphic OCaml
([automatic_cell.ml](../examples/automatic_cell.ml)):

<<< ../examples/automatic_cell.ml{caravan}

Its interface exposes a shared handle and a contents resource
([automatic_cell.mli](../examples/automatic_cell.mli)):

<<< ../examples/automatic_cell.mli{caravan}

`shared cell` is a duplicable invariant handle: it can be copied and shared between
threads, giving each thread access to the same invariant. The ownership protected
by the invariant is not duplicated. `contents cell value` is a resource describing
the abstract contents. Ordinary `requires` clauses hold around the
operation; `atomic requires` and `atomic ensures` describe its abstract logical step.
A client supplies the contents resource at that step and receives it back, changed
by `set` or preserved by `read`. The client uses the `shared cell` invariant handle
but need not know the invariant's definition or the concrete resources it protects.

The companion proof supplies the state interpretation and linearization points
([automatic_cell.proof](../examples/automatic_cell.proof)):

<<< ../examples/automatic_cell.proof{proof}

With all three files saved together, verify the example with:

```bash
caravan automatic_cell.ml
```

Here the state record has just one field, `value`. The invariant relates it to the
contents of the concrete atomic; `view contents` exposes that value to clients.
`initially` establishes the initial state after allocation.

In the action declaration, `compare_and_set cell _ value` describes the concrete
step: `_` leaves the expected old value unspecified, and `value` is the value
being installed. `~> { s with value = value }` gives the resulting proof state.
`linearizes set` says that this transition also fulfills `set`'s atomic contract.
The outline's `performs replace` attaches that action to the implementation's CAS.
On success, both the concrete cell and the abstract contents change together.
On failure, neither changes on behalf of this invocation, and the call retries.

The read needs no state-changing action. Its `commit` annotation establishes the
atomic postcondition at `Atomic.get`, using the observed contents as its result.

Caravan generates the invariant-opening, restoration, and atomic-update plumbing.
It still checks that the chosen steps establish the contracts. The proof establishes
partial correctness of completed operations, not eventual CAS success.

State-based proofs can also describe growing fields and facts about earlier states,
with generated history support. The
[history-based Michael–Scott queue](https://github.com/nyu-acsys/caravan/tree/main/test/saturn/michael_scott_queue)
uses this for helping and FIFO reasoning. This automation is optional: the next
example manages its atomic update explicitly.

## Manual mode: open and commit the update {#sec:manual-mode-open-and-commit-the-update}

This smaller example exports a contents predicate directly. It has no generated
state record or shared invariant; its atomic contract lets a client use the
resource at the read's abstract step.

Implementation ([manual_cell.ml](../examples/manual_cell.ml)):

<<< ../examples/manual_cell.ml{caravan}

Interface ([manual_cell.mli](../examples/manual_cell.mli)):

<<< ../examples/manual_cell.mli{caravan}

Proof ([manual_cell.proof](../examples/manual_cell.proof)):

<<< ../examples/manual_cell.proof{proof}

Verify this example with:

```bash
caravan manual_cell.ml
```

The constructor folds the owned atomic into `contents`. In `proof read`,
`at (Atomic.get cell)` selects the implementation's read expression and attaches
the closure `fun step -> ...` to it. Caravan binds `step` to that selected
operation: `step ()` executes the original `Atomic.get cell` and returns its
observed value. The proof code before and after that call prepares and restores
resources around the read. `step` is a proof-level placeholder, not another
function added to the executable OCaml program; its name is freely chosen.

This access closure makes `read` manual. `Read` is a typed atomic-update facade
for the operation named `read`:

1. `Read.bind ()` obtains the current call's update token.
2. `Read.access token cell` opens the atomic precondition and returns its implicit
   value parameter.
3. `unfold` exposes concrete ownership for the actual `step ()` read.
4. `fold` restores the abstract resource, and `Read.commit` establishes the atomic
   postcondition using the observed result.

The closure must execute the attached operation exactly once, unconditionally,
and return its unchanged runtime result. Preparation and restoration are checked
proof code. This is the external-outline form of an inline
`(*@ Ghost.scope (fun step -> ...) *)` annotation. Explicit `(*@ manual *)` also
selects manual mode. Automatic `commit`, `returning`, and `performs` annotations
are rejected in manual functions, so the two styles cannot both manage one update.

Manual proofs can open and close direct invariants, call structural lemmas around
atomic accesses, abort an update by restoring its precondition, or let another
thread commit a stored token. Raven checks permissions and atomicity in all cases.
The complete [segment-based queue](https://github.com/nyu-acsys/caravan/tree/main/test/saturn/michael_scott_queue_lseg)
illustrates this style, including helping and exceptional completion.

## Carry ghost information without changing runtime code {#sec:carry-ghost-information-without-changing-runtime-code}

An ordinary `Ghost.scope` wraps one runtime operation with proof code. Its local
ghost bindings do not escape the closure. To carry a ghost value between accesses,
use `Ghost.State.scope`: it receives the current ghost state as a second parameter
and returns `(runtime_result, next_ghost_state)`. This pair is proof-only; the
attached OCaml expression still produces just its original runtime result.

Each function starts with ghost state `()`. Consecutive state scopes in a lexical
sequence receive the preceding scope's output; its type may change between scopes.
Ordinary `Ghost.scope` annotations and unannotated accesses preserve that state.

For example, download [ghost_scopes.ml](../examples/ghost_scopes.ml) and its
[companion proof](../examples/ghost_scopes.proof). The proof defines a predicate
owning the cell:

<<< ../examples/ghost_scopes.proof{proof}

The implementation saves the initial contents as ghost state, replaces the
runtime contents, and checks the saved value afterward:

<<< ../examples/ghost_scopes.ml{caravan}

Run `caravan ghost_scopes.ml`. The first `Ghost.State.scope` takes unit state and
saves the read value. The middle `Ghost.scope` unfolds `contents` to expose the
ownership needed by `Atomic.exchange`, checks its returned old value, and folds
the predicate with the new value `7`. That ordinary scope returns the unchanged
exchange result and preserves the carried ghost state. The last state scope
therefore receives the original contents as `saved`, although the runtime cell now
contains `7`. Its output resets the ghost state to `()`.

Here the function owns the cell's contents exclusively. A saved ghost value alone
does not imply that shared memory still contains that value; it records a past
observation. Any claim about current contents still needs an ownership or invariant
proof.

Composition is lexical rather than a state merge along control flow. Branches,
match arms, and loop bodies inherit the enclosing ghost state, but their updates
do not escape those regions. A loop also does not carry a changed ghost state
from one iteration to the next. Use a loop invariant for iteration reasoning;
`invariant (fun saved -> proposition)` can refer to the inherited ghost state.

Contracts can also declare ghost inputs and results. Calls pass these through
access scopes; `Ghost.returns` supplies ghost results at runtime return points.
Ghost values, allocations, and updates have no runtime effects. Manual and
automatic modes share the same translation of executable OCaml and the same
primitive models.

Continue with [OCaml coverage](./ocaml-subset) and the
[semantic conventions](./semantics).
