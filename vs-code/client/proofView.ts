import * as vscode from 'vscode';
import { proofViewScheme, showProofViewCommand, type ProofViewResult } from '../shared/protocol';
import { registerReadOnlyViews } from './readOnlyView';

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
  return registerReadOnlyViews({
    scheme: proofViewScheme, command: showProofViewCommand, language: 'caravan-proof',
    suffix: '.proof-view', name: 'proof', links,
    errorText: message => `(* Caravan proof view unavailable.\nSave the implementation and its companion files, then try again.\n${message.replace(/\*\)/g, '* )')}\n*)\n`
  }, request, subscribe);
}
