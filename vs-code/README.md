<table>
<tr>
<td width="200"><img width="200" src="https://raw.githubusercontent.com/nyu-acsys/caravan/HEAD/.github/assets/logo.png" alt="Caravan logo"/></td>
<td>

# Caravan VS Code Extension

VS Code integration for [Caravan](https://github.com/nyu-acsys/caravan), a verifier
for multicore OCaml programs. This directory contains the extension's source.
For installation, configuration, and everyday use, see the
[user guide](MARKETPLACE.md); the documentation below covers development and releases.

New to Caravan? Start with the **[project introduction and examples](https://github.com/nyu-acsys/caravan#readme)**.

</td>
</tr>
</table>

## Development prerequisites

Install Node.js and npm, and build [Caravan](../README.md#building) with Z3 on
its runtime path. The extension uses OCaml Platform for OCaml editing and base
syntax highlighting; install it in the VS Code instance used for testing.
Published platform packages bundle the verifier and its dependencies, while local
extension builds use an installed or development toolchain.

## Building from Source

From the repository's `vs-code/` directory:

```bash
$ npm ci
$ npm test
$ npx @vscode/vsce package --readme-path MARKETPLACE.md
$ code --install-extension caravan-0.1.0.vsix
```

Use the filename produced by `vsce package` if the extension version has changed.
This creates an unbundled development package. It includes the language server
and its runtime dependencies; configure your installed Caravan and Z3 as described below.

`npm test` compiles the client and server and tests verification diagnostics,
related locations, warnings, streamed member statuses, cancellation, and stale-result
handling over LSP.
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

### Selecting a development toolchain

To test a local Caravan build in an opam switch, use settings such as:

```json
{
  "caravan.executable": "opam",
  "caravan.arguments": ["exec", "--switch=my-switch", "--", "caravan"]
}
```

OCaml Platform's selected opam sandbox does not automatically configure Caravan.
You can also set `caravan.executable` to the absolute path of a local Caravan build,
such as `/path/to/caravan/_build/default/bin/caravan.exe`.

### Verifier interface

The client launches `out/server/server.js` over IPC. The server invokes Caravan
with Raven's `--lsp-mode --lsp-annotations` options. Reports use the same JSON
shape: `errors`, `dependencies`, `annotations`, `members`, `references`, and
`symbols`. Source lines are one-based and columns are UTF-8 byte offsets; the
server converts them to LSP UTF-16 positions. The annotation table includes
external contracts in Raven's `InheritedContract` format and Caravan `ProofStep`
entries with source locations and annotation text. The `members` table describes
source declarations: `id`, `name`, `kind`, the declaration's location fields,
`extent`, optional `parent`, `group`, `status`, `cached`, `own_status`, `own_checks`, and
`counts`. Locations use `file`, `start_line`, `start_col`, `end_line`, and `end_col`;
`extent` spans the declaration's text. `status` includes nested members and
prerequisites, while `own_status` and `own_checks` describe its own backend checks.
Group `counts` count source leaves by status. Status values are `unchecked`,
`checked`, `trusted`, `verified`, `pending`, `skipped`, `timeout`, and `failed`.
`cached` is true only for entirely cached verified members or groups; clients
accept its absence in reports from older tools as false.
The reference and symbol tables remain empty.

Verification uses `caravan --server`, with Raven's JSON-line framing. Each request
contains `id`, `cwd`, `args`, and `partial: true`; `args` includes the editor options
and implementation path. Partial responses contain the same `id`, a `phase`
(`typed`, `scheduled`, or `progress`), and `partial`, a JSON report encoded as a
string. The final response contains `id`, `exit`, `stdout`, and `stderr`, with the
final report in `stdout`. The extension starts one process per verification run;
it does not keep a persistent verifier session. Successful proof fingerprints are
reused across runs through Raven's cache in extension storage. Fingerprints cover
the obligation and its dependencies, including contracts and relevant automatic
lemmas, and are tied to the executable build and solver version. Parsing, type
checking, translation and lowering still run to establish the current obligations.
An older executable that explicitly rejects `--server` falls back to a batch run.
This compatibility path omits the automatic cache option.
A malformed stream is reported as an error without a batch retry.

Streamed reports use the same worker queue, cancellation, dirty-input checks, and
dependency/run generations as final results. A companion-file change invalidates
the run even when the implementation document's version has not changed.

Adding `--lsp-annotations-only` collects these attachments and an unchecked member
inventory using the same front-end resolution as verification, without generating
Raven code or running SMT checks. Discovery never marks a member verified.
The server shares this mode, worker queue, and dependency cache between contract
hovers, status lenses, and proof views, so ongoing verification does not delay discovery.
The client requests a combined view with `caravan/proofView` and refreshes its
read-only virtual document on `caravan/proofViewChanged` notifications.

`caravan/ravenView` uses the same metadata dependency graph to reject unsaved or
changed inputs, then runs `--emit-rav` with the configured launcher, environment,
working directory, and include paths. Translation shares the bounded discovery
queue and supports cancellation; it does not run the solver or update verification
results. The client shares the proof view's read-only document lifecycle and
refresh notifications. The virtual document has a `.rav` filename, letting VS Code
use the Raven extension's language association and highlighting when installed,
or plain text otherwise. Caravan does not register a Raven grammar. The Raven
extension selects file URIs for verification, so the generated view is not sent
to its verifier.

`caravan --manifest` reports its version, editor protocol, minimum Z3 version,
OCaml compiler version, and linked Raven API version. A native archive carries
the same `manifest.json` alongside `bin/`, `lib/ocaml/`, and `licenses/`.

## Releasing Bundled Packages

The verifier and extension have separate release tags within this repository:

1. Set the verifier version in `dune-project` and `lib/config/caravan_config.ml`, choose the immutable
   Raven commit in [`RAVEN_REVISION`](../RAVEN_REVISION), and the Z3 release in
   [`Z3_VERSION`](../Z3_VERSION). The Raven commit must be available on GitHub.
2. Push a `vX.Y.Z` verifier tag. The [native release workflow](../.github/workflows/release.yml)
   builds and checks relocated Linux x64, macOS arm64, and Windows x64 bundles and creates a
   draft release with archives, `manifest.json`, and `SHA256SUMS`. Review and
   publish that release.
3. Set [`CARAVAN_VERSION`](CARAVAN_VERSION) to the published verifier tag.
   Publish the verifier release before packaging the extension. Set the extension
   version in [`package.json`](package.json).
4. Push `vscode-vX.Y.Z` for that extension version. The [package workflow](../.github/workflows/package.yml)
   verifies the pinned archives and creates a draft release containing the
   platform VSIXs. Review them before publishing or uploading to the Marketplace.

Later compatible verifier releases are offered to installed extensions without
rebuilding them. Release a new extension when its code or editor protocol support
changes, or to refresh the toolchain available on the first offline run.

Linux bundles are built on Ubuntu 24.04 to match the pinned Z3 distribution
and require a compatible system with glibc 2.39 or later.

Windows builds use native Python for packaging and include the runtime DLLs
required by Caravan and Z3, with their accompanying notices. Both the archive
smoke test and updater installation test remove compiler paths from the environment
before verification, so the packaged tools must work independently of the build
machine's opam and MinGW setup.

## Extension documentation

[`MARKETPLACE.md`](MARKETPLACE.md) is the user-facing listing shown inside VS Code.
Packaging selects it with `--readme-path MARKETPLACE.md`; `.vscodeignore` excludes
this developer README to avoid a collision with the packaged `readme.md`.
Keep build, protocol, and release details here, and user setup and usage there.
The [package workflow](../.github/workflows/package.yml) uses the same selection
for every platform package.
