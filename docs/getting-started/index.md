# Getting started

Caravan checks OCaml code with specifications written in comments. You can run
it from the command line or use its VS Code extension to develop proofs alongside
normal OCaml editing.

## Set up Caravan

For VS Code, install
[OCaml Platform](https://marketplace.visualstudio.com/items?itemName=ocamllabs.ocaml-platform)
and the Caravan extension. The
[extension instructions](https://github.com/nyu-acsys/caravan/tree/main/vs-code#readme)
cover installation from a VSIX and building a development package.

A platform-specific Caravan package contains the verifier, its linked Raven
library, Z3, and matching OCaml standard-library interfaces. An unbundled
development package uses a separately installed toolchain; see
[building from source](#build-from-source) below.

## Verify a first file

Create `negate.ml` with the following contents, or
[download the example](../examples/negate.ml):

```caravan
let negate (flag : bool) = not flag
(*@ result = negate flag ensures result === not flag *)
```

The contract names the returned value `result` and states that it equals the
negation of the input. `===` is specification equality. The annotation is an
ordinary comment to the OCaml compiler.

In VS Code, save the file and run **Caravan: Verify Saved File** from the Command
Palette. Saving also verifies automatically by default. A successful check shows
**Caravan: verified** in the status bar and a verified status above the function.

With `caravan` on your command-line path, run:

```bash
caravan negate.ml
```

From a source checkout, use `dune exec -- caravan /path/to/negate.ml` instead.
Caravan reports `Verification successful.` when the contract is proved for every
Boolean input.

To see a failure, change the contract to `ensures result === flag` and verify
again. The editor reports the failed proof obligation at the OCaml source, with
related specification locations where available.

## Read the editor results

Verification statuses appear for individual members, with summaries for modules
and functors. A member stays marked as checking until its generated proof checks
finish. A successful reused result is marked **(cached)**; editing the code or its
dependencies marks earlier results outdated until verification runs again.

The extension verifies saved files. Save edits before checking, including edits
to companion interfaces and proofs. For project libraries, Caravan must use the
same OCaml compiler version as their compiled artifacts. The extension's
**Caravan: Show Verifier Version** command reports its toolchain version; its
README explains executable overrides, opam launchers, and include paths.

## Separate contracts and proofs

Contracts exported to clients can be placed in a sibling `.mli` file. More
detailed proofs can live in a sibling `.proof` file, including predicates,
invariants, lemmas, and annotations attached to implementation steps. Caravan
checks these companions together with the `.ml` implementation.

The extension displays external contracts and short proof annotations in the
implementation. Hover for their details, follow their source links, or run
**Caravan: Show Proof View** for a read-only view combining the code and its proof.

## Build from source

Caravan currently requires OCaml 5.5 and Raven's API library. From a new checkout,
create a matching opam switch and install the Raven revision recorded by Caravan:

```bash
git clone https://github.com/nyu-acsys/caravan.git
cd caravan
opam switch create caravan 5.5.0
eval $(opam env --switch=caravan)
opam pin add raven-ivl "git+https://github.com/nyu-acsys/raven.git#$(cat RAVEN_REVISION)"
opam install . --deps-only --with-test
dune build
```

[Z3](https://github.com/Z3Prover/z3) version 4.13.0 or later must be on the path.
Run the example from the checkout with:

```bash
dune exec -- caravan docs/examples/negate.ml
```

To work against a Raven source checkout instead of its opam pin, place that
checkout next to Caravan and link it into the workspace:

```bash
mkdir -p vendor
ln -s ../../raven vendor/raven
```

Use a Raven revision compatible with the one in `RAVEN_REVISION`. The full
[build instructions](https://github.com/nyu-acsys/caravan#building) and
[extension setup guide](https://github.com/nyu-acsys/caravan/tree/main/vs-code#readme)
cover further configuration.

## Continue with concurrent code

The [Saturn case studies](https://github.com/nyu-acsys/caravan/tree/main/test/saturn)
show ownership contracts and concurrent data-structure proofs in larger programs.
The [Raven tutorial](https://nyu-acsys.github.io/raven/tutorial/) explains the
underlying separation logic. For Caravan's annotation syntax and supported OCaml
constructs, use the [repository reference](https://github.com/nyu-acsys/caravan#readme).
