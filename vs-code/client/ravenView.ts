import * as vscode from 'vscode';
import { ravenViewScheme, showRavenViewCommand, type RavenViewResult } from '../shared/protocol';
import { registerReadOnlyViews } from './readOnlyView';

export function registerRavenViews(
  request: (uri: string, token: vscode.CancellationToken) => Promise<RavenViewResult>,
  subscribe: (listener: () => void) => vscode.Disposable
): vscode.Disposable {
  return registerReadOnlyViews({
    scheme: ravenViewScheme, command: showRavenViewCommand,
    suffix: '.rav', name: 'Raven',
    errorText: message => `/* Caravan Raven view unavailable.\nSave the implementation and its companion files, then try again.\n${message.replace(/\*\//g, '* /')}\n*/\n`
  }, request, subscribe);
}
