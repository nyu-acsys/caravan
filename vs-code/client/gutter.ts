import * as vscode from 'vscode';
import * as path from 'node:path';

export type LineMessages = Map<number, string[]>;
export interface GutterMarkers {
  errors: LineMessages;
  warnings: LineMessages;
  related: LineMessages;
}

type MarkerKind = 'error' | 'warning' | 'related';
const priority: Record<MarkerKind, number> = { error: 0, warning: 1, related: 2 };

/** Related locations can point into another document, so inspect the whole collection. */
export function gutterMarkers(target: vscode.Uri,
  entries: readonly [vscode.Uri, readonly vscode.Diagnostic[]][]): GutterMarkers {
  const lines = new Map<number, { kind: MarkerKind; messages: string[] }>();
  const add = (line: number, kind: MarkerKind, message: string): void => {
    const entry = lines.get(line);
    if (entry) {
      if (priority[kind] < priority[entry.kind]) entry.kind = kind;
      if (!entry.messages.includes(message)) entry.messages.push(message);
    } else {
      lines.set(line, { kind, messages: [message] });
    }
  };
  const targetUri = target.toString();
  for (const [uri, diagnostics] of entries) {
    for (const diagnostic of diagnostics) {
      if (diagnostic.source !== 'Caravan') continue;
      if (uri.toString() === targetUri) {
        const kind = diagnostic.severity === vscode.DiagnosticSeverity.Error ? 'error'
          : diagnostic.severity === vscode.DiagnosticSeverity.Warning ? 'warning' : undefined;
        if (kind) add(diagnostic.range.start.line, kind, diagnostic.message);
      }
      for (const related of diagnostic.relatedInformation ?? []) {
        if (related.location.uri.toString() === targetUri) {
          add(related.location.range.start.line, 'related', related.message);
        }
      }
    }
  }
  const result: GutterMarkers = { errors: new Map(), warnings: new Map(), related: new Map() };
  for (const [line, { kind, messages }] of lines) {
    const selected = kind === 'error' ? result.errors : kind === 'warning' ? result.warnings : result.related;
    selected.set(line, messages);
  }
  return result;
}

export function registerGutterMarkers(context: vscode.ExtensionContext): vscode.Disposable {
  const icon = (name: string): vscode.Uri => vscode.Uri.file(
    context.asAbsolutePath(path.join('images', 'gutter', `${name}.svg`)));
  const decoration = (name: MarkerKind): vscode.TextEditorDecorationType =>
    vscode.window.createTextEditorDecorationType({
      light: { gutterIconPath: icon(`${name}-light`) },
      dark: { gutterIconPath: icon(`${name}-dark`) },
      gutterIconSize: 'contain'
    });
  const types = { error: decoration('error'), warning: decoration('warning'), related: decoration('related') };
  const update = (editor: vscode.TextEditor): void => {
    const markers = supported(editor.document) ? gutterMarkers(editor.document.uri, vscode.languages.getDiagnostics())
      : { errors: new Map(), warnings: new Map(), related: new Map() };
    const decorations = (messages: LineMessages): vscode.DecorationOptions[] =>
      [...messages].filter(([line]) => line >= 0 && line < editor.document.lineCount).map(([line, text]) => ({
        range: new vscode.Range(line, 0, line, 0),
        hoverMessage: text.reduce((hover, message, index) => {
          if (index > 0) hover.appendMarkdown('\n\n');
          return hover.appendText(message);
        }, new vscode.MarkdownString())
      }));
    editor.setDecorations(types.error, decorations(markers.errors));
    editor.setDecorations(types.warning, decorations(markers.warnings));
    editor.setDecorations(types.related, decorations(markers.related));
  };
  const refresh = (): void => vscode.window.visibleTextEditors.forEach(update);
  refresh();
  return vscode.Disposable.from(types.error, types.warning, types.related,
    vscode.window.onDidChangeVisibleTextEditors(refresh),
    vscode.languages.onDidChangeDiagnostics(refresh));
}

function supported(document: vscode.TextDocument): boolean {
  return document.uri.scheme === 'file' &&
    ((document.languageId === 'ocaml' && document.uri.path.endsWith('.ml')) ||
      (document.languageId === 'ocaml.interface' && document.uri.path.endsWith('.mli')) ||
      (document.languageId === 'caravan-proof' && document.uri.path.endsWith('.proof')));
}
