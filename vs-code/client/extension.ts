import * as vscode from 'vscode';
import * as path from 'node:path';
import { LanguageClient, LanguageClientOptions, ServerOptions, State, TransportKind } from 'vscode-languageclient/node';

import { verificationStateNotification, verifyNotification, toolchainNotification, type VerificationState, type VerificationStateParams } from '../shared/protocol';
import { VerifierUpdates } from './updates';

let client: LanguageClient | undefined;

function supported(document: vscode.TextDocument): boolean {
  return document.uri.scheme === 'file' &&
    ((document.languageId === 'ocaml' && document.uri.path.endsWith('.ml')) ||
      (document.languageId === 'ocaml.interface' && document.uri.path.endsWith('.mli')) ||
      (document.languageId === 'caravan-proof' && document.uri.path.endsWith('.proof')));
}

export async function activate(context: vscode.ExtensionContext): Promise<void> {
  const output = vscode.window.createOutputChannel('Caravan');
  const status = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 10);
  status.command = 'caravan.verify';
  const states = new Map<string, VerificationStateParams>();
  let unavailable = false;
  const updates = new VerifierUpdates(context, output, async selection => {
    if (client?.isRunning()) await client.sendNotification(toolchainNotification, {
      executable: selection.executable, bundleRoot: selection.bundleRoot });
  });
  const toolchain = await updates.refresh();
  updates.register();
  const refresh = (): void => {
    const document = vscode.window.activeTextEditor?.document;
    if (!document || !supported(document)) {
      status.hide();
      return;
    }
    const saved = states.get(document.uri.toString());
    const state = document.isDirty ? 'outdated' : unavailable ? 'unavailable' :
      saved && saved.version === document.version ? saved.state : 'unchecked';
    const icons: Record<VerificationState, string> = {
      unchecked: 'circle-outline', outdated: 'circle-slash', verifying: 'sync~spin',
      verified: 'pass', verifiedWithWarnings: 'warning', failed: 'error', unavailable: 'warning'
    };
    const label = state === 'verifiedWithWarnings' ? 'verified with warnings' : state;
    status.text = `$(${icons[state]}) Caravan: ${label}`;
    status.color = state === 'verifiedWithWarnings' ? new vscode.ThemeColor('editorWarning.foreground') : undefined;
    status.tooltip = saved?.version === document.version && saved.state === state && saved.message ?
      saved.message : state === 'outdated' ? 'Save the file before verifying.' : 'Verify the saved file with Caravan.';
    status.show();
  };
  const serverOptions: ServerOptions = {
    run: { module: context.asAbsolutePath(path.join('out', 'server', 'server.js')), transport: TransportKind.ipc },
    debug: { module: context.asAbsolutePath(path.join('out', 'server', 'server.js')), transport: TransportKind.ipc }
  };
  const fileWatcher = vscode.workspace.createFileSystemWatcher('**/*.{ml,mli,proof}');
  context.subscriptions.push(fileWatcher);
  const clientOptions: LanguageClientOptions = {
    initializationOptions: () => {
      const selected = updates.current ?? toolchain;
      return { toolchain: { executable: selected.executable, bundleRoot: selected.bundleRoot } };
    },
    documentSelector: [
      { scheme: 'file', language: 'ocaml', pattern: '**/*.ml' },
      { scheme: 'file', language: 'ocaml.interface', pattern: '**/*.mli' },
      { scheme: 'file', language: 'caravan-proof', pattern: '**/*.proof' }
    ],
    synchronize: { configurationSection: 'caravan', fileEvents: fileWatcher },
    outputChannel: output
  };
  client = new LanguageClient('caravan', 'Caravan', serverOptions, clientOptions);
  const activeClient = client;
  context.subscriptions.push(output, status,
    activeClient.onNotification(verificationStateNotification, (value: VerificationStateParams) => {
      const document = vscode.workspace.textDocuments.find(item => item.uri.toString() === value.uri);
      if (!document || value.version !== document.version) return;
      states.set(value.uri, value);
      refresh();
    }),
    activeClient.onDidChangeState(event => {
      unavailable = event.newState !== State.Running;
      if (unavailable) states.clear();
      refresh();
    }),
    vscode.window.onDidChangeActiveTextEditor(refresh),
    vscode.workspace.onDidChangeTextDocument(event => {
      states.delete(event.document.uri.toString());
      refresh();
    }),
    vscode.workspace.onDidCloseTextDocument(document => {
      states.delete(document.uri.toString());
      refresh();
    }),
    vscode.commands.registerCommand('caravan.verify', async () => {
      const document = vscode.window.activeTextEditor?.document;
      if (!document || !supported(document)) {
        void vscode.window.showInformationMessage('Open an OCaml .ml, .mli, or Caravan .proof file to verify.');
        return;
      }
      if (document.isDirty) {
        void vscode.window.showInformationMessage('Save the file before verifying with Caravan.');
        return;
      }
      if (!activeClient.isRunning()) {
        void vscode.window.showErrorMessage('The Caravan language server is unavailable. See the Caravan output channel.');
        return;
      }
      await activeClient.sendNotification(verifyNotification, { uri: document.uri.toString() });
    })
  );
  refresh();
  try {
    await activeClient.start();
    const latest = updates.current;
    if (latest && (latest.executable !== toolchain.executable || latest.bundleRoot !== toolchain.bundleRoot)) {
      await activeClient.sendNotification(toolchainNotification, { executable: latest.executable, bundleRoot: latest.bundleRoot });
    }
    void updates.check(false);
  } catch (error) {
    unavailable = true;
    refresh();
    output.appendLine(`Could not start Caravan language server: ${String(error)}`);
    void vscode.window.showErrorMessage('Could not start the Caravan language server. See the Caravan output channel.');
  }
}

export async function deactivate(): Promise<void> {
  await client?.stop();
  client = undefined;
}
