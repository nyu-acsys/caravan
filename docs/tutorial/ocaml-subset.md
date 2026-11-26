# 5. OCaml coverage

Caravan uses OCaml's typed program, but accepts a subset of OCaml rather than
every type-correct program. Unsupported constructs normally produce a source
error. Existing OCaml libraries also need contracts: being accepted by the OCaml
compiler does not make an arbitrary library call verifiable.

## Expressions, types, and effects {#sec:expressions-types-and-effects}

| Area | Supported | Important restrictions |
| --- | --- | --- |
| Values | `int`, `bool`, `unit`, tuples, lists, options, variants, immutable records, arrays. | No general support for strings, floats, or objects. |
| Control flow | `let`, `if`, pattern matching, sequencing, recursive functions, `while` and `for` loops. | Supply loop invariants when the inferred facts are insufficient; `variant` annotations on executable functions and loops are not yet supported. |
| Functions | Named first-order functions, fully supplied labelled and optional arguments, local helpers and captures, recursion, and rank-one polymorphism. | No general partial applications, function-valued parameters, returned closures, or callbacks beyond inline `List.fold_left` functions; no independently generalized helper that also depends on enclosing type parameters. |
| Data types | Parameterized variants and records, including mutable records and mutable inline constructor records, regular recursive types, and aliases. | Immutable inline constructor records and nonregular recursive data types are unsupported. |
| Mutable state | References, mutable records, arrays (`Array.make`, `length`, `get`, `set`), supported `Atomic` operations, and explicit frozen/relaxed field disciplines. | Default reads/writes require ownership; advanced modes require [visibility and journal proofs](./weak-memory). Array indices and lengths must be shown in bounds; array literals and the higher-order `Array` functions are unsupported. |
| GADTs | Constant witness types, including Saturn's result-selection witnesses, and payload constructors indexed by sets of constant polymorphic-variant tags. | No arbitrary dependent payloads, existential payload types, or runtime polymorphic variants. |
| Exceptions | Declared exceptions, supported handlers, and normal and exceptional contracts. | Contracts must account for exceptional outcomes; this is not a model of every runtime or system exception. |
| Concurrency | Atomics, shared invariants, logically atomic contracts, explicit ghost resources, helping proofs, statically known polymorphic `Domain.spawn`/`Domain.join` tasks, native mutexes with ownership effects and task cleanup, and native conditions. | `Mutex.protect` is unsupported; blocking and deadlock freedom are not proved. |

Each array index is a cell of its own, which contracts own through `Array.cell a i`, as
in `own (Array.cell a i) v`; `Array.length a` is the array's fixed length. Ownership of
many entries is quantified, as in
`forall j : int. 0 <= j && j < Array.length a -> own (Array.cell a j) 0`. Reads and
writes of entries, as `a.(i)` and `a.(i) <- v`, can anchor proof scopes like field
accesses. Shared invariants can be quantified over entries too, as
`forall j : int. 0 <= j && j < Array.length locks -> Guard.is_mutex (Map.get ms j) (counts, j)`
for an array of mutexes each guarding one entry of `counts`; such a quantifier needs no
proof that the mutexes differ.

Generic functions are checked once with constraints on their type parameters,
rather than by verifying each concrete call separately. Those constraints preserve
source-value admissibility, including integer bounds and domains of nested
containers. Local helpers can capture enclosing values and type parameters.
Ordering on unconstrained generic values and explicitly quantified source type
annotations remain outside the supported subset.

Optional arguments retain their supplied option in contracts. For example:

```ocaml
let choose ?(value = 42) () = value
```

The companion proof can name that incoming option `requested`:

```proof
proof result = choose requested token
  ensures result === (match requested with None -> 42 | Some value -> value) = ()
```

`choose ()` supplies `None`, `choose ~value:7 ()` supplies `Some 7`, and
`choose ?value:requested ()` forwards the option. With `?value` and no default,
the source body also receives the option. With a default, the source body receives
the selected value. Defaults run inside the callee, after its precondition, only
for absent inputs; their effects and exceptions are checked with the rest of the
body. Defaults may refer to earlier parameters. Within the callee, defaults and parameter
pattern reads follow parameter order. Proof steps can annotate a default
expression, but facts exported there cannot be used on paths that skip it.

Mutable records may have type parameters. Their fields use the usual ownership
contracts; the same generic operation can store integers or Booleans:

```ocaml
type 'a cell = { mutable contents : 'a }

let replace cell value = cell.contents <- value
(*@ replace cell value
    requires own cell.contents before
    ensures own cell.contents value *)
```

Every field of a heap record requires ownership to read, including fields declared
immutable in OCaml. Parameterized record fields retain their source-value bounds
when generic operations are instantiated at concrete types.

GADT indices can restrict which constructors a value may have. For example:

```ocaml
type ('a, _) node =
  | Null : ('a, [> `Null ]) node
  | Node : { mutable value : 'a } -> ('a, [> `Node ]) node

and 'a link = Link : ('a, [< `Null | `Node ]) node -> 'a link [@@unboxed]
```

The type ``('a, [ `Node ]) node`` permits only `Node`, while `Link` can contain
`Null` or `Node`. Constructor payloads retain their ordinary type parameters and
ownership requirements. Constructor patterns may also appear directly in function
parameters; verification checks that their arguments match. Constant-tag rows can also occur in `.proof` type
annotations, using ``[ `Node ]``, ``[> `Node ]``, or ``[< `Null | `Node ]``.
These rows describe type indices; polymorphic-variant values are not supported.
This does not provide general GADT reasoning about arbitrary type equations or
existential payload types. Abstract constructor-set indices and polymorphic indices
shared between an argument and result are not yet supported; independent producer
rows and fixed constructor sets are supported.

Checked `variant` annotations currently apply to logical functions and lemmas in
`.proof` files. Executable functions and loops are verified for partial correctness,
without proving termination.

Assertions, loop invariants, and contracts carry proof obligations. For an exception
contract, use `raises Exception -> proposition` (or `atomic raises` for an atomic
outcome). A logical `pure` function can be used in specifications when it meets
Caravan's purity and termination requirements; arbitrary OCaml calls cannot be
embedded in a proposition.

## Domain tasks {#sec:domain-tasks}

Declare a facade in the companion `.proof` file for each operation to run in a
domain:

```proof
module Job = Ghost.Task (struct let operation = work end)
```

The operation needs an ordinary, explicit contract. A call such as
`Domain.spawn (fun () -> work cell)` transfers that contract's precondition to
the task. `Domain.join domain` recovers its normal postcondition or propagates a
declared exception with its exceptional postcondition. A named unit operation
can also be passed directly: `Domain.spawn work`.

Tasks and their callers may be polymorphic. Type arguments are inferred from the
call and carried by the handle resource, including type parameters that occur only
in captured arguments. For example, a task `work value` with contract
`ensures result === value` can be spawned at both `int` and `bool` in the same
client. Generic callers and functor bodies can use an existing task facade without
adding type arguments to the proof syntax.

Functors can also declare task facades in the matching `.proof` module. Repeat the
source functor's parameters in that module header, as for other proof declarations.
The task contract is checked with the generic body, including when the functor is
never applied. Repeated applicative applications share task identity; generative
applications keep their completion resources distinct. Facades respect the functor
result's signature boundary. This uses the shared generic translation; applications
that require an unsupported specialized proof body are rejected explicitly.

The spatial predicate `Job.handle domain cell` records the right to join this
task with captured argument `cell`. Use it in contracts when passing handles
between functions. Handles may be aliased, but the resource can be consumed only
once. OCaml itself allows repeated joins; the current verification contract
supports one resource-recovering join.

Task operations may also declare ghost inputs and results. A `Ghost.scope` attached
to `Domain.spawn` supplies the ghost inputs, using the same syntax as a checked
procedure call. The handle stores these inputs together with inferred precondition
witnesses. A scope attached to `Domain.join` receives the ghost results; they are
unavailable before joining. `Ghost.returns` supplies those results in the worker's
proof. When a handle crosses a function boundary, pass the declared ghost inputs
after the captured runtime arguments in its `Job.handle` predicate; inferred
precondition witnesses remain implicit. Past-fact witnesses follow the same transfer:
precondition snapshots are captured at spawn, and returned facts are recovered at
join.

Inline thunks must call a known task with captured values or constants. Put
computed arguments and more elaborate child code in a separately verified task;
Caravan does not move their effects into the parent. Logically atomic task
contracts are not yet supported. Joins need enough information to select a unique
task facade, from the handle's origin or its contract.

With a Mutex facade present, each spawned task receives a fresh execution owner
and an empty held-lock set. Implicit owner and held-set names in the worker's
context clause denote that child context; they are not captured from the parent.
Explicit ghost inputs retain their supplied values and must satisfy the worker's
precondition in the child's context. For example, a parent's held token cannot
authorize a child to unlock its mutex.

Caravan generates a checked completion adapter that calls the actual worker and
requires empty holdings before completion, on both normal and exceptional exits.
This obligation is checked even for a task facade that is never spawned. The
native fork/join implementation is trusted to execute the designated operation;
the adapter checks that its contract justifies the resources returned by join.
Spawn and join preserve the parent's execution context. Join returns the worker's
promised resources without exposing a live child context or changing lock owners.
The same mechanism supports polymorphic tasks, ghost results and history facts.
These are partial-correctness guarantees; blocking and deadlock freedom are not
proved.

The [parallel stack-drain client](https://github.com/nyu-acsys/caravan/tree/main/test/saturn/stack_drain)
demonstrates shared access: a shared invariant holds the stack's exclusive
ownership, and each worker receives its own ghost counter resource. Both joins
return the completed worker resources, allowing the parent to recover the stack
and drain twenty elements. Its runtime code follows Saturn's tutorial with integer
worker IDs and a named loop counter; all implementation annotations are in the
companion `.proof` file.

## Mutex critical sections {#sec:mutex-critical-sections}

Runtime code uses ordinary `Mutex.create`, `Mutex.lock`, `Mutex.unlock`, and
`Mutex.try_lock`. A companion proof chooses the resource protected by a mutex:

```proof
module Cell : Ghost.MutexResource with type t = int ref = struct
  type t = int ref
  predicate resource (cell : t) =
    exists value : int. own cell.contents value && 0 <= value
end
module Guard = Ghost.Mutex (Cell)
```

The explicit `with type` exposes the context's carrier equality; an ordinary colon
ascription keeps it abstract. The local concrete predicate definition remains
available for folding and unfolding. The resource is a spatial predicate, not a
resource algebra, and need not be exclusive itself.

A `Ghost.scope` around creation installs the resource:

```proof
at (Mutex.create ()) (fun create ->
  fold Cell.resource cell;
  let mutex = create () in
  Guard.initialize mutex cell;
  mutex)
```

`Guard.is_mutex mutex cell` is a persistent association. Successful acquisition
returns `Cell.resource cell` and an exclusive `Guard.held mutex self` token;
unlocking consumes both. Open the cell predicate after locking and fold it before
unlocking, using the usual proof scopes.

Each executable function has a hidden execution owner and held-lock set. By
default, an ordinary function preserves that set on both normal and exceptional
exits. This is checked against its body; Caravan does not insert cleanup. Trusted
imports implicitly promise the same preservation. In a contract, name the entry
context and require availability when acquiring an existing mutex:

```proof
requires Ghost.Mutex.context self held &&
  not (Finset.mem mutex held) && Guard.is_mutex mutex cell
```

These names are inferred contract witnesses, without explicit ghost-call adapters.
The context clause describes the existing hidden context; it does not introduce
another copy or let the proof choose a different execution owner. There can be
one direct context conjunct per contract channel. A fresh mutex is absent from
the current held set. Recursive locking and wrong-owner unlocking fail their
preconditions, accounting for OCaml's programmer-error exceptions.

Helpers that acquire or release a lock can state the resulting held set in an
ordinary postcondition. For example, this contract allows `acquire` to return
with the mutex held:

```proof
proof acquire mutex cell
  requires Ghost.Mutex.context self held &&
    not (Finset.mem mutex held) && Guard.is_mutex mutex cell
  ensures Ghost.Mutex.context self (Finset.union held (Finset.singleton mutex)) &&
    Guard.is_mutex mutex cell && Guard.held mutex self && Cell.resource cell = ()
```

A release helper requires the held token and protected resource and states
`Ghost.Mutex.context self (Finset.diff held (Finset.singleton mutex))` on return.
The caller receives the updated context automatically through the ordinary call;
no extra ghost arguments are needed. The execution owner stays the same.

A `raises` clause can similarly specify the held set on that exceptional outcome.
Omitting a context clause requires preservation of the entry set independently
for the normal exit and each declared exceptional outcome, even if another exit
explicitly changes it. A bare `raises Exception` clause also preserves holdings.
Overlapping exception patterns impose all matching clauses, including their
preservation defaults.

Loops preserve the procedure's entry context by default. If the function acquires
a lock before entering a loop, give the loop an explicit context invariant, such
as `Ghost.Mutex.context self (Finset.union held (Finset.singleton mutex))`, along
with the protected data invariant. Context invariants remain required on an
exceptional exit from the loop too.

A failed `try_lock` grants no protected resource. If the current execution already
holds the mutex, it returns false and preserves the existing resources.

The same execution-context rules apply through checked module signatures and
functor parameters. Unit, curried and named-parameter functors can use Mutex and
Domain operations, and can declare their protected resource and facades in the
matching proof module. A functor's native accesses use its lexically bound facade;
other applications of that functor do not make that choice ambiguous. Compatible
contracts can name their context witnesses differently, or omit the names when
they are unused, without adding ghost arguments to calls. Imported operations
retain their existing contracts and implicitly promise context preservation.

Manual `Ghost.AU` proofs keep the same syntax. Their tokens internally retain the
originating call's context, including when tokens are aliased, stored in ghost
fields, or used in a helping proof. This metadata does not grant ownership of that
execution context to the helper.

Protected resources can also be polymorphic. For a source record `type 'a cell =
{ mutable value : 'a; mutex : Mutex.t }`, its companion proof can declare:

```proof
module Cell : Ghost.MutexResource with type 'a t = 'a cell = struct
  type 'a t = 'a cell
  predicate resource (cell : 'a t) =
    exists value : 'a. own cell.value value
end
module Guard = Ghost.Mutex (Cell)
```

Each value-type instance has its own checked resource implementation. Native
accesses require one unambiguous facade in their lexical proof environment.
Caravan infers its type arguments from the protected record receiver or a unique
matching carrier among the function's parameters and result. Ghost operations
can also use carrier types in the proof environment. Caravan rejects ambiguous
cases rather than guessing a type instance.

The [tutorial blocking stack](https://github.com/nyu-acsys/caravan/tree/main/test/ocaml5_tutorial/blocking_stack)
uses this mechanism with a polymorphic list. Its constructor returns ghost mutex
and condition handles, and its operation contracts take them as explicit ghost
arguments. This keeps invariant masks precise across calls. An access scope passes
the handles together as `invoke (mutex, condition)`; runtime calls stay unchanged.
`Mutex.protect` is not supported yet. The
[focused mutex examples](https://github.com/nyu-acsys/caravan/tree/main/test/translate/mutex)
show complete critical sections and exceptional cleanup.

### Native condition variables

`Condition.create`, `Condition.wait`, `Condition.signal`, and
`Condition.broadcast` are supported with a `Ghost.Mutex` facade. Associate a
condition with its mutex using `Guard.initialize_condition condition mutex`;
`Guard.is_condition condition mutex` records that persistent association.
`wait` requires the current owner to hold the associated mutex and its folded
resource. It releases the mutex while waiting, reacquires it on return, and
returns the refreshed resource. Since wakeups may be spurious, callers must
recheck their predicate in a loop. `signal` and `broadcast` require the
association, but do not require the mutex to be held and establish no guard or
protected-data guarantee.

The [condition regressions](https://github.com/nyu-acsys/caravan/tree/main/test/translate/condition)
show the basic contract and spurious-wakeup behavior. The
[Moonpool parker](https://github.com/nyu-acsys/caravan/tree/main/test/moonpool/parker)
is a larger example using waits and notifications together.

## Modules and functors {#sec:modules-and-functors}

Caravan supports ordinary and nested `module ... = struct ... end`, aliases,
named signatures, `.mli` abstraction, `open`, and `include` of modules, functor
applications, and structures. Export contracts in the signature; callers through an
interface use those contracts, not private implementation definitions. A signature
cannot restate the contract of an included function that has one. Opened and
included modules also bring their proof modules' predicates and lemmas into scope. Proof modules mirror source modules and may contain
logical types, predicates, invariants, lemmas, ghost fields, and resource-algebra
instances.

Supported source functors have named module parameters or unit parameters and a
structure body. Ordinary currying and partial application are supported. Argument
signatures may expose polymorphic operations, predicates, and abstract type
constructors such as `type 'a t`. Proofs are shared through Raven functors where
the generic representation supports the body; other supported bodies use separate
verified specializations.

Functor bodies and their companion proofs are verified at their declarations,
using the parameter signatures as abstract contracts. This includes functors that
are never applied; adding an application is not needed to check their bodies.

Repeated applicative applications to the same module share result identity;
aliases preserve that identity. Unit applications introduce fresh identities.
These distinctions matter for abstract types, heap fields, and proof resources.
The [stack-drain client](https://github.com/nyu-acsys/caravan/tree/main/test/saturn/stack_drain)
and [functor queue examples](https://github.com/nyu-acsys/caravan/tree/main/test/examples/functor_ms_queue)
show supported module-level reuse.

Important remaining module restrictions include:

- Recursive modules, local modules, and first-class modules. Higher-order and
  imported functors are not supported by the shared generic translation.
- Module initialization expressions, `include` of imported modules, and `open` of
  module expressions other than paths.
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
| `List.length` | Runtime calls return an OCaml `int`; specifications use total mathematical length. |
| `List.rev`, `List.rev_append` | List reversal, usable in implementations and specifications. |
| `List.fold_left` | Fully supplied calls with an inline two-parameter function, checked as a loop. |
| `Seq.empty`, `List.to_seq`, `List.of_seq` | Finite, reusable snapshots, described by `Seq.persistent sequence values`. |

The runtime `List.length` contract requires the length to fit in an OCaml `int`:

```caravan
let size values = List.length values
(*@ result = size values
    requires List.length values <= max_int
    ensures result = List.length values *)
```

The same expression in a specification denotes mathematical length even when
that bound does not hold.

For `List.fold_left`, attach an invariant to the call in the companion proof:
`at (List.fold_left callback initial values) invariant (fun accumulator remaining -> proposition)`.
The anchor must contain the actual inline callback. Tuple accumulator patterns are
supported; a third invariant parameter can name the inherited `Ghost.State` state.
Callback effects, proof scopes, and exceptions use the usual translation rules.

Snapshots remain usable after the originating data structure changes. User-defined
sequence producers, direct sequence-thunk calls, stateful/one-shot sequences, and
other higher-order list operations need further higher-order support. General `lazy`,
effect handlers, `Obj`, and first-class modules are outside the current subset.

The bundled [standard-library interfaces](https://github.com/nyu-acsys/caravan/tree/main/lib/stdlib)
state their precise contracts. Their `.proof` companions supply reusable checked
mathematical models and lemmas; clients do not reprove those facts. `Stdlib_model`
provides their logical models only in specifications. The
[next page](./semantics#sec:trusted-code-and-imports) describes what is trusted.
