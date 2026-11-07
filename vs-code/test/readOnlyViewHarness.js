const assert = require('node:assert/strict');
const Module = require('node:module');
const { URI } = require('vscode-uri');
const { proofViewScheme, showProofViewCommand, ravenViewScheme, showRavenViewCommand } = require('../out/shared/protocol');

class Disposable {
  constructor(action = () => {}) { this.action = action; }
  dispose() { this.action(); }
  static from(...items) { return new Disposable(() => items.forEach(item => item.dispose())); }
}
class EventEmitter {
  listeners = new Set();
  event = listener => {
    this.listeners.add(listener);
    return new Disposable(() => this.listeners.delete(listener));
  };
  fire(value) { for (const listener of [...this.listeners]) listener(value); }
  dispose() { this.listeners.clear(); }
}
class CancellationTokenSource {
  constructor() {
    this.emitter = new EventEmitter();
    this.token = { isCancellationRequested: false, onCancellationRequested: this.emitter.event };
  }
  cancel() { this.token.isCancellationRequested = true; this.emitter.fire(); }
  dispose() { this.emitter.dispose(); }
}
class CancellationError extends Error {}
const token = () => new CancellationTokenSource().token;
const range = (startLine = 0, startCharacter = 0, endLine = 0, endCharacter = 5) => ({
  start: { line: startLine, character: startCharacter }, end: { line: endLine, character: endCharacter }
});
const result = (text = 'proof text', target = 'file:///workspace/source.proof#L2,3') => ({
  text, links: [{ range: range(), target }]
});
const deferred = () => {
  let resolve, reject;
  const promise = new Promise((yes, no) => { resolve = yes; reject = no; });
  return { promise, resolve, reject };
};

function setup(request = async () => result(), kind = 'proof', language = 'plaintext') {
  const raven = kind === 'Raven';
  const commandName = raven ? showRavenViewCommand : showProofViewCommand;
  const close = new EventEmitter();
  const updates = new EventEmitter();
  const changed = [];
  const opened = [];
  const messages = [];
  const calls = [];
  const registrations = [];
  const documents = new Map();
  const refreshes = [];
  let provider, linkProvider, command;
  const vscode = {
    Uri: URI, EventEmitter, Disposable, CancellationTokenSource, CancellationError,
    ViewColumn: { Beside: -2 },
    Range: class {
      constructor(sl, sc, el, ec) { this.start = { line: sl, character: sc }; this.end = { line: el, character: ec }; }
    },
    DocumentLink: class {
      constructor(range, target) { this.range = range; this.target = target; }
    },
    commands: { registerCommand(name, callback) {
      assert.equal(name, commandName);
      command = callback;
      return new Disposable();
    } },
    workspace: {
      registerTextDocumentContentProvider(scheme, value) {
        registrations.push({ kind: 'content', scheme });
        provider = value;
        value.onDidChange(uri => {
          changed.push(uri);
          const document = documents.get(uri.toString());
          if (document) {
            const refreshing = value.provideTextDocumentContent(uri, token()).then(text => { document.text = text; });
            refreshes.push(refreshing);
            // The editor owns refresh errors, including superseded requests.
            void refreshing.catch(() => {});
          }
        });
        return new Disposable();
      },
      onDidCloseTextDocument: close.event,
      async openTextDocument(uri) {
        const key = uri.toString();
        if (documents.has(key)) return documents.get(key);
        const text = await provider.provideTextDocumentContent(uri, token());
        const document = { uri, text, languageId: language };
        documents.set(key, document);
        return document;
      }
    },
    languages: {
      registerDocumentLinkProvider(selector, value) {
        registrations.push({ kind: 'links', selector });
        linkProvider = value;
        return new Disposable();
      },
      async setTextDocumentLanguage(document, languageId) {
        // VS Code closes and reopens a document when its language changes.
        close.fire(document);
        document.languageId = languageId;
        return document;
      }
    },
    window: {
      activeTextEditor: undefined,
      async showTextDocument(document, options) { opened.push({ document, options }); },
      showInformationMessage(message) { messages.push(message); },
      showErrorMessage(message) { messages.push(message); }
    }
  };
  const load = Module._load;
  let registerProofViews;
  const modulePath = require.resolve(raven ? '../out/client/ravenView' : '../out/client/proofView');
  delete require.cache[modulePath];
  delete require.cache[require.resolve('../out/client/readOnlyView')];
  try {
    Module._load = function (name, ...rest) {
      return name === 'vscode' ? vscode : load.call(this, name, ...rest);
    };
    const module = require(modulePath);
    registerProofViews = raven ? module.registerRavenViews : module.registerProofViews;
  } finally { Module._load = load; }
  const disposable = registerProofViews((uri, cancellation) => {
    calls.push({ uri, token: cancellation });
    return request(uri, cancellation);
  }, updates.event);
  return {
    calls, changed, opened, messages, registrations, disposable,
    async refreshed() { await Promise.all(refreshes.splice(0)); },
    get provider() { return provider; },
    get links() { return linkProvider; },
    async show(source) {
      vscode.window.activeTextEditor = { document: {
        uri: typeof source === 'string' ? URI.parse(source) : source.uri,
        isDirty: typeof source === 'string' ? false : source.isDirty
      } };
      return command();
    },
    refresh() { updates.fire(); },
    close(uri) { documents.delete(uri.toString()); close.fire({ uri }); }
  };
}

module.exports = { setup, token, range, result, deferred, CancellationError, CancellationTokenSource };
