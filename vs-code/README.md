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

Platform packages bundle Caravan, its linked Raven verifier, Z3, and matching
OCaml standard-library interfaces. No separate tool installation is needed for
self-contained programs. Bundles are built for Linux x64, macOS arm64, and Windows x64.
For other platforms or an unbundled development package, install
[Caravan and its dependencies](https://github.com/nyu-acsys/caravan#building).

The extension requires [OCaml Platform](https://marketplace.visualstudio.com/items?itemName=ocamllabs.ocaml-platform)
for normal OCaml editing and base syntax highlighting. Caravan adds highlighting
inside `(*@ ... *)` annotations and for `.proof` files, alongside Platform's
completion, navigation, and formatting.

## First Usage

Open your OCaml project in VS Code. A platform package uses its bundled toolchain
on the first run, including offline. Raven is linked into Caravan; updating
Caravan updates that verifier too, with no separate Raven executable to manage.

### Which verifier gets used

In order of precedence:

1. `caravan.executable`, if set: your development-build or launcher override.
2. A compatible toolchain installed by this extension, selected by the update channel.
3. The toolchain bundled with the extension.
4. `caravan` on your `PATH`, for unbundled development packages.

The bundled toolchain is a floor rather than a pin. On the default `stable`
channel, an older managed version cannot replace a newer bundled one. The `tag`
channel selects the release named by `caravan.caravanVersion`; `bundled` disables
managed versions and update checks.

On startup, at most once a day, the extension checks for a compatible Caravan
release and offers to install it. **Nothing is downloaded without asking**, apart
from release metadata. Run **Caravan: Update Verifier** to check on demand,
**Caravan: Show Verifier Version** to see the selected toolchain, or
**Caravan: Use Bundled Verifier** to return to the shipped one. An explicit
executable override always wins and disables update offers.

Each update supplies Caravan, Z3, and matching OCaml interfaces together.
Downloads are checked against `SHA256SUMS`; a temporary installation must answer
`--manifest` and verify a small program before it becomes selectable. A failed or
cancelled install leaves previous versions available. A release with an editor
protocol the extension does not understand is declined.

Caravan type-checks with its own OCaml compiler. Existing library artifacts must
match that compiler version, shown by **Caravan: Show Verifier Version**. Rebuild
libraries with that compiler, pin an appropriate Caravan release, or use a
matching development build. For a particular opam switch, use settings such as:

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

### Verifying a file

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

Verification settings can be set per workspace or folder. Update settings apply
to the VS Code window:

* `caravan.executable`: Override automatic selection with an executable or
  launcher program. Empty by default.
* `caravan.updateChannel`: `stable` (follow compatible releases, the default),
  `tag` (select a release), or `bundled` (use the shipped toolchain).
* `caravan.caravanVersion`: The release tag for the `tag` channel, e.g. `v0.1.0`.
* `caravan.checkForUpdates`: Check on startup, at most once a day. Defaults to
  `true`; installing still requires accepting the offer.
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
This creates an unbundled development package. It includes the language server
and its runtime dependencies; configure your installed Caravan and Z3 as above.

`npm test` compiles the client and server and tests verification diagnostics,
related locations, warnings, cancellation, and stale-result handling over LSP.
It also checks TextMate token scopes with Oniguruma and compares keyword coverage
with Caravan's specification lexer. Installer tests use local release fixtures,
checking version selection, compatibility, checksums, extraction, cancellation,
and atomic installation. Interactive coexistence with OCaml Platform is currently
checked manually.

To test a real native archive, set `CARAVAN_TEST_RELEASE_DIRECTORY` to a directory
containing the archive, `manifest.json`, and `SHA256SUMS` when running `npm test`.
The test installs through the updater and verifies the Saturn Treiber stack with
the relocated toolchain. Native release CI runs this check on each build platform.

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

`caravan --manifest` reports its version, editor protocol, minimum Z3 version,
OCaml compiler version, and linked Raven API version. A native archive carries
the same `manifest.json` alongside `bin/`, `lib/ocaml/`, and `licenses/`.

## Releasing Bundled Packages

The verifier and extension have separate release tags within this repository:

1. Set the verifier version in `lib/config/caravan_config.ml`, choose the immutable
   Raven commit in [`RAVEN_REVISION`](../RAVEN_REVISION), and the Z3 release in
   [`Z3_VERSION`](../Z3_VERSION). The Raven commit must be available on GitHub.
2. Push a `vX.Y.Z` verifier tag. The [native release workflow](../.github/workflows/release.yml)
   builds and checks relocated Linux x64, macOS arm64, and Windows x64 bundles and creates a
   draft release with archives, `manifest.json`, and `SHA256SUMS`. Review and
   publish that release.
3. Set [`CARAVAN_VERSION`](CARAVAN_VERSION) to the published verifier tag. It is
   initially `unreleased`, which prevents accidental packaging against a
   nonexistent release. Set the extension version in [`package.json`](package.json).
4. Push `vscode-vX.Y.Z` for that extension version. The [package workflow](../.github/workflows/package.yml)
   verifies the pinned archives and creates a draft release containing the
   platform VSIXs. Review them before publishing or uploading to the Marketplace.

Later compatible verifier releases are offered to installed extensions without
rebuilding them. Release a new extension when its code or editor protocol support
changes, or to refresh the toolchain available on the first offline run.

Windows builds use native Python for packaging and include the runtime DLLs
required by Caravan and Z3, with their accompanying notices. Both the archive
smoke test and updater installation test remove compiler paths from the environment
before verification, so the packaged tools must work independently of the build
machine's opam and MinGW setup.
