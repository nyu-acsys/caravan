import * as vscode from 'vscode';
import { openContractCommand, type ContractLocation } from '../shared/protocol';

function object(value: unknown): value is Record<string, unknown> {
  return typeof value === 'object' && value !== null;
}

function position(value: unknown): value is ContractLocation['range']['start'] {
  return object(value) && Number.isInteger(value.line) && (value.line as number) >= 0
    && Number.isInteger(value.character) && (value.character as number) >= 0;
}

function location(value: unknown): value is ContractLocation {
  if (!object(value) || typeof value.uri !== 'string' || !object(value.range)
    || !position(value.range.start) || !position(value.range.end)) return false;
  const { start, end } = value.range;
  return start.line < end.line || (start.line === end.line && start.character <= end.character);
}

export function registerContractNavigation(): vscode.Disposable {
  return vscode.commands.registerCommand(openContractCommand, async (value: unknown) => {
    if (!location(value)) return;
    const uri = vscode.Uri.parse(value.uri);
    if (uri.scheme !== 'file') return;
    const { start, end } = value.range;
    return vscode.window.showTextDocument(uri, { preview: true,
      selection: new vscode.Range(start.line, start.character, end.line, end.character) });
  });
}
