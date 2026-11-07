import * as vscode from 'vscode';

interface ViewResult { text: string }
interface ViewOptions<T extends ViewResult> {
  scheme: string;
  command: string;
  language?: string;
  suffix: string;
  name: string;
  errorText: (message: string) => string;
  links?: (result: T) => vscode.DocumentLink[];
}

interface View {
  uri: vscode.Uri;
  source: vscode.Uri;
  generation: number;
  text?: string;
  links: vscode.DocumentLink[];
  pending?: vscode.CancellationTokenSource;
}

export function registerReadOnlyViews<T extends ViewResult>(
  options: ViewOptions<T>,
  request: (uri: string, token: vscode.CancellationToken) => Promise<T>,
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

  const content = vscode.workspace.registerTextDocumentContentProvider(options.scheme, {
    onDidChange: changed.event,
    async provideTextDocumentContent(uri, token) {
      if (disposed || token.isCancellationRequested) throw new vscode.CancellationError();
      const key = uri.toString();
      let view = views.get(key);
      if (!view) {
        const source = vscode.Uri.parse(uri.query, true);
        if (source.scheme !== 'file' || !source.path.endsWith('.ml')) {
          throw new Error(`Caravan ${options.name} views require an OCaml implementation file.`);
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
          throw new Error(`The Caravan language server returned an invalid ${options.name} view.`);
        }
        current.links = options.links?.(result) ?? [];
        current.text = result.text;
        return result.text;
      } catch (error) {
        if (stale() || error instanceof vscode.CancellationError) throw new vscode.CancellationError();
        current.links = [];
        const message = error instanceof Error ? error.message : String(error);
        return options.errorText(message);
      } finally {
        listener.dispose();
        cancellation.dispose();
        if (current.pending === cancellation) current.pending = undefined;
      }
    }
  });
  const navigation = options.links ? vscode.languages.registerDocumentLinkProvider({ scheme: options.scheme }, {
    provideDocumentLinks(document) { return views.get(document.uri.toString())?.links ?? []; }
  }) : new vscode.Disposable(() => {});
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
  const command = vscode.commands.registerCommand(options.command, async () => {
    const active = vscode.window.activeTextEditor?.document;
    const document = active?.uri.scheme === options.scheme
      ? { uri: vscode.Uri.parse(active.uri.query, true), isDirty: false } : active;
    if (!document || document.uri.scheme !== 'file' || !/\.(ml|mli|proof)$/.test(document.uri.path)) {
      void vscode.window.showInformationMessage(`Open an OCaml .ml, .mli, or Caravan .proof file to show its ${options.name} view.`);
      return;
    }
    if (document.isDirty) {
      void vscode.window.showInformationMessage(`Save the file before opening the Caravan ${options.name} view.`);
      return;
    }
    const source = document.uri.with({ path: document.uri.path.replace(/\.(ml|mli|proof)$/, '.ml'),
      query: '', fragment: '' });
    const uri = source.with({ scheme: options.scheme, path: source.path.replace(/\.ml$/, options.suffix),
      query: source.toString() });
    const existing = views.get(uri.toString());
    if (existing) {
      invalidate(existing);
      changed.fire(uri);
    }
    try {
      let document = await vscode.workspace.openTextDocument(uri);
      if (options.language && document.languageId !== options.language) {
        const key = uri.toString();
        changingLanguage.add(key);
        try { document = await vscode.languages.setTextDocumentLanguage(document, options.language); }
        finally { changingLanguage.delete(key); }
      }
      await vscode.window.showTextDocument(document, { viewColumn: vscode.ViewColumn.Beside, preview: true });
    } catch (error) {
      if (!(error instanceof vscode.CancellationError)) {
        const message = error instanceof Error ? error.message : String(error);
        void vscode.window.showErrorMessage(`Could not open the Caravan ${options.name} view: ${message}`);
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
