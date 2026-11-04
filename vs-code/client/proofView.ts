import * as vscode from 'vscode';
import { proofViewScheme, showProofViewCommand, type ProofViewResult } from '../shared/protocol';

interface View {
  uri: vscode.Uri;
  source: vscode.Uri;
  generation: number;
  text?: string;
  links: vscode.DocumentLink[];
  pending?: vscode.CancellationTokenSource;
}

function object(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null;
}

function position(value: unknown): value is { line: number; character: number } {
  return object(value) && Number.isSafeInteger(value.line) && (value.line as number) >= 0
    && Number.isSafeInteger(value.character) && (value.character as number) >= 0;
}

function links(result: ProofViewResult): vscode.DocumentLink[] {
  if (!Array.isArray(result.links)) return [];
  const lines = result.text.split('\n');
  const validPosition = (point: { line: number; character: number }): boolean =>
    point.line < lines.length && point.character <= lines[point.line].replace(/\r$/, '').length;
  const items: vscode.DocumentLink[] = [];
  for (const item of result.links as unknown[]) {
    if (!object(item) || typeof item.target !== 'string' || !item.target.startsWith('file:/') || !object(item.range)
      || !position(item.range.start) || !position(item.range.end)) continue;
    const { start, end } = item.range;
    if (!validPosition(start) || !validPosition(end) || start.line > end.line
      || (start.line === end.line && start.character >= end.character)) continue;
    try {
      const target = vscode.Uri.parse(item.target, true);
      if (target.scheme !== 'file' || !target.path.startsWith('/')) continue;
      items.push(new vscode.DocumentLink(new vscode.Range(start.line, start.character,
        end.line, end.character), target));
    } catch { /* Ignore malformed navigation targets. */ }
  }
  return items;
}

export function registerProofViews(
  request: (uri: string, token: vscode.CancellationToken) => Promise<ProofViewResult>,
  subscribe: (listener: () => void) => vscode.Disposable
): vscode.Disposable {
  const views = new Map<string, View>();
  const changingLanguage = new Set<string>();
  const changed = new vscode.EventEmitter<vscode.Uri>();
  let disposed = false;

  const invalidate = (view: View): void => {
    view.generation++;
    view.pending?.cancel();
    view.pending?.dispose();
    view.pending = undefined;
    view.text = undefined;
    view.links = [];
  };

  const content = vscode.workspace.registerTextDocumentContentProvider(proofViewScheme, {
    onDidChange: changed.event,
    async provideTextDocumentContent(uri, token) {
      if (disposed || token.isCancellationRequested) throw new vscode.CancellationError();
      const key = uri.toString();
      let view = views.get(key);
      if (!view) {
        const source = vscode.Uri.parse(uri.query, true);
        if (source.scheme !== 'file' || !source.path.endsWith('.ml')) {
          throw new Error('Caravan proof views require an OCaml implementation file.');
        }
        view = { uri, source, generation: 0, links: [] };
        views.set(key, view);
      }
      if (view.text !== undefined) return view.text;
      invalidate(view);
      const current = view;
      const generation = current.generation;
      const cancellation = new vscode.CancellationTokenSource();
      current.pending = cancellation;
      const listener = token.onCancellationRequested(() => cancellation.cancel());
      const stale = (): boolean => disposed || cancellation.token.isCancellationRequested
        || token.isCancellationRequested || views.get(key) !== current
        || generation !== current.generation;
      try {
        const result = await request(current.source.toString(), cancellation.token);
        if (stale()) throw new vscode.CancellationError();
        if (!result || typeof result.text !== 'string') {
          throw new Error('The Caravan language server returned an invalid proof view.');
        }
        current.links = links(result);
        current.text = result.text;
        return result.text;
      } catch (error) {
        if (stale() || error instanceof vscode.CancellationError) throw new vscode.CancellationError();
        current.links = [];
        const message = error instanceof Error ? error.message : String(error);
        // Error text replaces the previous proof when a refresh fails.
        const text = `(* Caravan proof view unavailable.\nSave the implementation and its companion files, then try again.\n${message.replace(/\*\)/g, '* )')}\n*)\n`;
        return text;
      } finally {
        listener.dispose();
        cancellation.dispose();
        if (current.pending === cancellation) current.pending = undefined;
      }
    }
  });
  const navigation = vscode.languages.registerDocumentLinkProvider({ scheme: proofViewScheme }, {
    provideDocumentLinks(document) { return views.get(document.uri.toString())?.links ?? []; }
  });
  const updates = subscribe(() => {
    for (const view of views.values()) {
      invalidate(view);
      changed.fire(view.uri);
    }
  });
  const closed = vscode.workspace.onDidCloseTextDocument(document => {
    const key = document.uri.toString();
    if (changingLanguage.has(key)) return;
    const view = views.get(key);
    if (view) invalidate(view);
    views.delete(key);
  });
  const command = vscode.commands.registerCommand(showProofViewCommand, async () => {
    const document = vscode.window.activeTextEditor?.document;
    if (!document || document.uri.scheme !== 'file' || !/\.(ml|mli|proof)$/.test(document.uri.path)) {
      void vscode.window.showInformationMessage('Open an OCaml .ml, .mli, or Caravan .proof file to show its proof view.');
      return;
    }
    if (document.isDirty) {
      void vscode.window.showInformationMessage('Save the file before opening the Caravan proof view.');
      return;
    }
    const source = document.uri.with({ path: document.uri.path.replace(/\.(ml|mli|proof)$/, '.ml'),
      query: '', fragment: '' });
    const uri = source.with({ scheme: proofViewScheme, path: source.path.replace(/\.ml$/, '.proof-view'),
      query: source.toString() });
    const existing = views.get(uri.toString());
    if (existing) {
      invalidate(existing);
      changed.fire(uri);
    }
    try {
      let proof = await vscode.workspace.openTextDocument(uri);
      if (proof.languageId !== 'caravan-proof') {
        const key = uri.toString();
        changingLanguage.add(key);
        try { proof = await vscode.languages.setTextDocumentLanguage(proof, 'caravan-proof'); }
        finally { changingLanguage.delete(key); }
      }
      await vscode.window.showTextDocument(proof, { viewColumn: vscode.ViewColumn.Beside, preview: true });
    } catch (error) {
      if (!(error instanceof vscode.CancellationError)) {
        const message = error instanceof Error ? error.message : String(error);
        void vscode.window.showErrorMessage(`Could not open the Caravan proof view: ${message}`);
      }
    }
  });
  return vscode.Disposable.from(command, content, navigation, updates, closed, changed,
    new vscode.Disposable(() => {
      disposed = true;
      for (const view of views.values()) invalidate(view);
      views.clear();
    }));
}
