import * as vscode from 'vscode';
import * as path from 'node:path';
import { CompatibilityError, compareVersions, fetchRelease, installRelease, normalizeVersion, platformAsset,
  readManifest, resolveToolchain, type Toolchain } from './verifier';

const day = 24 * 60 * 60 * 1000;

export class VerifierUpdates implements vscode.Disposable {
  private generation = 0;
  private selected?: Toolchain;
  private checking?: Promise<void>;
  private transfer?: AbortController;
  private disposed = false;

  constructor(private readonly context: vscode.ExtensionContext,
    private readonly output: vscode.OutputChannel,
    private readonly changed: (toolchain: Toolchain) => Promise<void>) {}

  get current(): Toolchain | undefined { return this.selected; }

  private configuration(): vscode.WorkspaceConfiguration {
    return vscode.workspace.getConfiguration('caravan');
  }

  async resolve(): Promise<Toolchain> {
    const configuration = this.configuration();
    const channel = configuration.get<string>('updateChannel', 'stable');
    return resolveToolchain({ extensionPath: this.context.extensionPath,
      storagePath: this.context.globalStorageUri.fsPath,
      channel: channel === 'tag' || channel === 'bundled' ? channel : 'stable',
      version: configuration.get<string>('caravanVersion', '') });
  }

  async refresh(): Promise<Toolchain> {
    const generation = ++this.generation;
    const selection = await this.resolve();
    if (this.disposed || generation !== this.generation) return selection;
    const previous = this.selected;
    this.selected = selection;
    if (!previous || previous.executable !== selection.executable || previous.bundleRoot !== selection.bundleRoot) {
      await this.changed(selection);
    }
    return selection;
  }

  register(): void {
    this.context.subscriptions.push(this,
      vscode.commands.registerCommand('caravan.updateVerifier', () => this.check(true)),
      vscode.commands.registerCommand('caravan.showVerifierVersion', () => this.showVersion()),
      vscode.commands.registerCommand('caravan.useBundledVerifier', async () => {
        const target = vscode.workspace.workspaceFolders?.length
          ? vscode.ConfigurationTarget.Workspace : vscode.ConfigurationTarget.Global;
        await this.configuration().update('updateChannel', 'bundled', target);
        if (this.configuredExecutable()) {
          void vscode.window.showInformationMessage('The configured Caravan executable still takes precedence. Clear caravan.executable to use the bundled verifier.');
        }
      }),
      vscode.workspace.onDidChangeConfiguration(event => {
        if (['updateChannel', 'caravanVersion'].some(key => event.affectsConfiguration(`caravan.${key}`))) {
          void this.refresh().then(() => this.check(false, true)).catch(error => this.report(error, true));
        }
      }));
  }

  private configuredExecutable(): string {
    return vscode.workspace.getConfiguration('caravan', vscode.window.activeTextEditor?.document.uri)
      .get<string>('executable', '').trim();
  }

  private async activeToolchain(): Promise<Toolchain & { cwd?: string }> {
    const uri = vscode.window.activeTextEditor?.document.uri;
    const configuration = vscode.workspace.getConfiguration('caravan', uri);
    const executable = configuration.get<string>('executable', '').trim();
    if (!executable) return this.resolve();
    const workspace = uri && vscode.workspace.getWorkspaceFolder(uri)?.uri.fsPath;
    const directory = workspace ?? (uri?.scheme === 'file' ? path.dirname(uri.fsPath) : process.cwd());
    const cwd = path.resolve(directory, configuration.get<string>('cwd', '') || '.');
    return { source: 'configured', executable: /[/\\]/.test(executable) ? path.resolve(cwd, executable) : executable,
      arguments: configuration.get<string[]>('arguments', []), cwd };
  }

  private async showVersion(): Promise<void> {
    try {
      const toolchain = await this.activeToolchain();
      const manifest = toolchain.manifest ?? await readManifest(toolchain.executable, toolchain.bundleRoot, toolchain.arguments, toolchain.cwd);
      void vscode.window.showInformationMessage(`Caravan ${manifest.version} (${toolchain.source}), OCaml ${manifest.ocaml_version}, Raven API ${manifest.raven_api_version}. ${toolchain.executable}`);
    } catch (error) { this.report(error, true); }
  }

  check(manual: boolean, force = false): Promise<void> {
    if (!this.checking) {
      this.checking = this.checkOnce(manual, force).finally(() => { this.checking = undefined; });
    }
    return this.checking;
  }

  private async checkOnce(manual: boolean, force: boolean): Promise<void> {
    const generation = this.generation;
    const configuration = this.configuration();
    const channel = configuration.get<string>('updateChannel', 'stable');
    if (this.disposed) return;
    if (this.configuredExecutable()) {
      if (manual) void vscode.window.showInformationMessage('Caravan is using your configured executable. Clear caravan.executable to use bundled or managed toolchains.');
      return;
    }
    if (channel === 'bundled') {
      if (manual) void vscode.window.showInformationMessage('Caravan updates are disabled by the bundled channel. Choose stable or tag to install updates.');
      return;
    }
    if (!manual && (!configuration.get<boolean>('checkForUpdates', true)
      || (!force && Date.now() - this.context.globalState.get<number>('verifier.lastCheck', 0) < day))) return;
    if (!platformAsset()) {
      if (manual) void vscode.window.showInformationMessage(`No bundled Caravan release is available for ${process.platform}-${process.arch}. Configure caravan.executable instead.`);
      return;
    }
    const tag = channel === 'tag' ? configuration.get<string>('caravanVersion', '').trim() : undefined;
    if (channel === 'tag' && !tag) {
      if (manual) void vscode.window.showInformationMessage('Set caravan.caravanVersion to the release to install.');
      return;
    }
    let accepted = false;
    try {
      await this.context.globalState.update('verifier.lastCheck', Date.now());
      const release = await fetchRelease(tag);
      if (this.disposed || generation !== this.generation) return;
      const current = await this.resolve();
      let version = current.manifest?.version;
      if (!version && current.source === 'path') {
        try { version = (await readManifest(current.executable)).version; } catch { /* A legacy PATH build need not support manifests. */ }
      }
      const equal = version && normalizeVersion(version) === normalizeVersion(release.manifest.version);
      if (equal || (channel !== 'tag' && version && compareVersions(release.manifest.version, version) <= 0)) {
        if (manual) void vscode.window.showInformationMessage(`Caravan ${version} is up to date.`);
        return;
      }
      const answer = await vscode.window.showInformationMessage(
        `Caravan ${release.manifest.version} is available with OCaml ${release.manifest.ocaml_version}. Library artifacts must match this compiler. Install the toolchain?`, 'Install', 'Later');
      if (answer !== 'Install' || this.disposed || generation !== this.generation) return;
      accepted = true;
      await vscode.window.withProgress({ location: vscode.ProgressLocation.Notification,
        title: 'Installing Caravan toolchain', cancellable: true }, async (progress, token) => {
        const abort = new AbortController();
        this.transfer = abort;
        const cancellation = token.onCancellationRequested(() => abort.abort());
        if (token.isCancellationRequested) abort.abort();
        try {
          await installRelease(release, this.context.globalStorageUri.fsPath, {
            signal: abort.signal, onProgress: message => progress.report({ message }) });
        } finally {
          cancellation.dispose();
          if (this.transfer === abort) this.transfer = undefined;
        }
      });
      if (this.disposed) return;
      await this.refresh();
      void vscode.window.showInformationMessage(`Caravan ${release.manifest.version} installed.`);
    } catch (error) {
      if (!this.disposed && !(error instanceof Error && error.name === 'AbortError')) this.report(error, manual || accepted || error instanceof CompatibilityError);
    }
  }

  private report(error: unknown, notify: boolean): void {
    const message = error instanceof Error ? error.message : String(error);
    this.output.appendLine(`Verifier update: ${message}`);
    if (notify) void vscode.window.showErrorMessage(`Caravan: ${message}`);
  }

  dispose(): void {
    this.disposed = true;
    this.generation++;
    this.transfer?.abort();
  }
}
