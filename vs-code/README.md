<table>
<tr>
<td width="200"><img width="200" src="https://raw.githubusercontent.com/nyu-acsys/caravan/HEAD/.github/assets/logo.png" alt="Caravan logo"/></td>
<td>

# Caravan VS Code Extension

VS Code integration for [Caravan](https://github.com/nyu-acsys/caravan), a verifier
for multicore OCaml programs. The extension highlights specifications and proof
files, reports verification errors in the editor, and tracks verification status.

New to Caravan? Start with the **[project introduction and examples](https://github.com/nyu-acsys/caravan#readme)**.
The instructions below cover setup, day-to-day use, and building the extension.

</td>
</tr>
</table>

## Prerequisites

Install [Caravan and its dependencies](https://github.com/nyu-acsys/caravan#building),
including its matching OCaml compiler, Raven, and Z3. This extension uses your
installed tools; it does not bundle them.

The extension requires [OCaml Platform](https://marketplace.visualstudio.com/items?itemName=ocamllabs.ocaml-platform)
for normal OCaml editing and base syntax highlighting. Caravan adds highlighting
inside `(*@ ... *)` annotations and for `.proof` files, alongside Platform's
completion, navigation, and formatting.

## First Usage

Open your OCaml project in VS Code with Caravan and Z3 on the editor's `PATH`.
For a particular opam switch, put settings such as these in your workspace:

```json
{
  "caravan.executable": "opam",
  "caravan.arguments": ["exec", "--switch=my-switch", "--", "caravan"],
  "caravan.includePaths": ["_build/default/lib"]
}
```

OCaml Platform's selected opam sandbox does not automatically configure Caravan.
You can also set `caravan.executable` to the absolute path of a local Caravan build,
such as `/path/to/caravan/_build/default/bin/caravan.exe`.

Open an annotated `.ml`, its `.mli`, or a `.proof` file. Save the file to verify it,
or run **Caravan: Verify Saved File** from the Command Palette. Clicking the
**Caravan:** status item also verifies the active file. For `.mli` and `.proof`
files, Caravan checks the sibling `.ml` implementation with its interface and
proof; a missing implementation is reported as unavailable.

Errors and warnings appear in the Problems panel and editor, with related source
locations. The status bar tracks the active file and its current version: unchecked,
outdated, verifying, verified, verified with warnings, failed, or unavailable.
Successful verification with warnings has a yellow indicator. Editing a file
invalidates its result and stops obsolete verifier processes; older results cannot
replace the current state. At most two verifier processes run concurrently.

This version verifies saved files. Save edits before running verification;
opening a file alone does not verify it. Changes to open dependencies or OCaml and
proof files in the workspace invalidate results. Closed dependencies outside the
workspace are not watched yet.

Caravan compiles and verifies the saved source without running a separate Dune
build. Build included libraries first so that their interfaces and compilation
artifacts are available. Verification requires a trusted workspace. If the tool
is unavailable, inspect the **Caravan** output channel for details.

## Configuration

This extension provides the following settings, which can be set per workspace
or folder:

* `caravan.executable`: The Caravan executable or launcher program. Defaults to
  `caravan` on VS Code's inherited `PATH`.
* `caravan.arguments`: Arguments to the launcher, before Caravan's verification
  flags and source path. Defaults to `[]`. For opam, use the example above.
* `caravan.cwd`: The working directory. Empty by default, using the containing
  workspace folder, or the file's directory outside a workspace. Relative paths
  are resolved from that directory.
* `caravan.includePaths`: Directories passed to Caravan with `-I`, resolved from
  the working directory. Defaults to `[]`.
* `caravan.smtTimeout`: The time limit in milliseconds for each SMT query.
  Defaults to `10000`.
* `caravan.verifyOnSave`: Verify supported files after saving. Defaults to `true`.

The executable is launched directly without a shell. Give the program and each
argument separately; do not put shell quoting or a complete command line into a
setting. Setting changes invalidate previous verification results.

## Building from Source

From the repository's `vs-code/` directory:

```bash
$ npm ci
$ npm test
$ npx @vscode/vsce package
$ code --install-extension caravan-0.1.0.vsix
```

Use the filename produced by `vsce package` if the extension version has changed.
The package includes the language server and its runtime dependencies. Caravan
and Z3 must be installed separately as described above.

`npm test` compiles the client and server and tests verification diagnostics,
related locations, warnings, cancellation, and stale-result handling over LSP.
It also checks TextMate token scopes with Oniguruma and compares keyword coverage
with Caravan's specification lexer. Interactive coexistence with OCaml Platform
is currently checked manually.

To develop without installing a VSIX, compile with `npm run compile` and launch
an Extension Development Host:

```bash
$ code --extensionDevelopmentPath="$PWD" /path/to/ocaml/workspace
```

Install OCaml Platform in the development host and configure Caravan there.
Check `.ml` and `.mli` annotations, `.proof` highlighting, manual verification,
verification after save, edits during verification, and a missing executable.

### Verifier interface

The client launches `out/server/server.js` over IPC. The server invokes Caravan
with Raven's `--lsp-mode --lsp-annotations` options. Reports use the same JSON
shape: `errors`, `dependencies`, `annotations`, `members`, `references`, and
`symbols`. Source lines are one-based and columns are UTF-8 byte offsets; the
server converts them to LSP UTF-16 positions. The annotation, member, reference,
and symbol tables are currently empty.
