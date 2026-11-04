const test = require('node:test');
const assert = require('node:assert/strict');
const Module = require('node:module');
const { URI } = require('vscode-uri');
const { proofViewScheme, showProofViewCommand } = require('../out/shared/protocol');

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

function setup(request = async () => result()) {
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
      assert.equal(name, showProofViewCommand);
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
        const document = { uri, text, languageId: 'plaintext' };
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
  const modulePath = require.resolve('../out/client/proofView');
  delete require.cache[modulePath];
  try {
    Module._load = function (name, ...rest) {
      return name === 'vscode' ? vscode : load.call(this, name, ...rest);
    };
    ({ registerProofViews } = require(modulePath));
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

test('proof views use a readonly content provider, proof language, and a separate editor', async t => {
  const h = setup();
  t.after(() => h.disposable.dispose());
  await h.show('file:///workspace/example.mli');
  assert.deepEqual(h.registrations, [
    { kind: 'content', scheme: proofViewScheme },
    { kind: 'links', selector: { scheme: proofViewScheme } }
  ]);
  assert.equal(h.calls[0].uri, 'file:///workspace/example.ml');
  const { document, options } = h.opened[0];
  assert.equal(document.uri.scheme, proofViewScheme);
  assert.equal(document.uri.path, '/workspace/example.proof-view');
  assert.equal(document.text, 'proof text');
  assert.equal(document.languageId, 'caravan-proof');
  assert.deepEqual(options, { viewColumn: -2, preview: true });
  const [link] = h.links.provideDocumentLinks(document);
  assert.equal(link.target.toString(), URI.parse('file:///workspace/source.proof#L2,3').toString());
  assert.deepEqual(link.range.start, { line: 0, character: 0 });
  assert.deepEqual(link.range.end, { line: 0, character: 5 });
});

test('native companion URIs roundtrip spaces, hashes, Unicode, drives, and network authorities', async t => {
  const h = setup();
  t.after(() => h.disposable.dispose());
  for (const source of [
    URI.from({ scheme: 'file', path: '/workspace/λ # contract.ml' }),
    URI.from({ scheme: 'file', path: '/workspace/λ # contract.mli' }),
    URI.from({ scheme: 'file', path: '/workspace/λ # contract.proof' }),
    URI.from({ scheme: 'file', path: '/C:/Users/Test #/λ.proof' }),
    URI.from({ scheme: 'file', authority: 'server', path: '/share/Test #/λ.mli' })
  ]) {
    const expected = source.with({ path: source.path.replace(/\.(ml|mli|proof)$/, '.ml') });
    await h.show({ uri: source, isDirty: false });
    const virtual = h.opened.at(-1).document.uri;
    assert.equal(URI.parse(virtual.toString()).query, expected.toString());
    h.close(virtual);
    await h.provider.provideTextDocumentContent(URI.parse(virtual.toString()), token());
    assert.equal(h.calls.at(-1).uri, expected.toString());
    assert.equal(virtual.path.endsWith('.proof-view'), true);
    h.close(virtual);
  }
});

test('unsupported and unsaved active documents explain how to open the saved-file view', async t => {
  const h = setup();
  t.after(() => h.disposable.dispose());
  for (const source of ['untitled:test.ml', 'file:///workspace/readme.txt']) await h.show(source);
  await h.show({ uri: URI.parse('file:///workspace/source.proof'), isDirty: true });
  assert.equal(h.calls.length, 0);
  assert.equal(h.opened.length, 0);
  assert.match(h.messages[0], /Open an OCaml/);
  assert.match(h.messages[2], /Save the file/);
});

test('showing an already-open proof view retries errors and refreshes its cached editor', async t => {
  let answer = new Error('The Caravan language server is unavailable.');
  const h = setup(async () => {
    if (answer instanceof Error) throw answer;
    return answer;
  });
  t.after(() => h.disposable.dispose());
  await h.show('file:///workspace/source.ml');
  const document = h.opened[0].document;
  assert.match(document.text, /proof view unavailable/);
  assert.equal(h.calls.length, 1);
  answer = result('recovered proof');
  await h.show('file:///workspace/source.proof');
  await h.refreshed();
  assert.equal(h.opened[1].document, document);
  assert.equal(document.text, 'recovered proof');
  assert.equal(h.calls.length, 2);
  assert.equal(h.links.provideDocumentLinks(document).length, 1);
  answer = result('changed disk proof');
  await h.show('file:///workspace/source.mli');
  await h.refreshed();
  assert.equal(document.text, 'changed disk proof');
  assert.equal(h.calls.length, 3);
});

test('malformed links and executable URI schemes cannot become navigation targets', async t => {
  const valid = { range: range(), target: 'file:///workspace/source.ml#L1,2' };
  const h = setup(async () => ({ text: 'proof text', links: [valid, null, {},
    { ...valid, target: 'command:execute' }, { ...valid, target: 'https://example.com' },
    { ...valid, target: 'file:relative.ml' }, { ...valid, target: 5 },
    { ...valid, range: range(-1) }, { ...valid, range: range(0, 7, 0, 5) },
    { ...valid, range: range(0, 0, 1, 0) }, { ...valid, range: range(0, 0, 0, 50) },
    { ...valid, range: range(0, 0, 0, 0) }, { ...valid, range: range(0.5) }
  ] }));
  t.after(() => h.disposable.dispose());
  await h.show('file:///workspace/source.ml');
  const links = h.links.provideDocumentLinks(h.opened[0].document);
  assert.equal(links.length, 1);
  assert.equal(links[0].target.toString(), URI.parse(valid.target).toString());
});

test('notifications clear stale links, refresh content, and replace failed views with guidance', async t => {
  let answer = result();
  const h = setup(async () => {
    if (answer instanceof Error) throw answer;
    return answer;
  });
  t.after(() => h.disposable.dispose());
  await h.show('file:///workspace/source.ml');
  const document = h.opened[0].document;
  h.refresh();
  assert.equal(h.changed[0].toString(), document.uri.toString());
  assert.deepEqual(h.links.provideDocumentLinks(document), []);
  answer = result('new proof text', 'file:///workspace/source.mli#L5,2');
  assert.equal(await h.provider.provideTextDocumentContent(document.uri, token()), 'new proof text');
  assert.equal(h.links.provideDocumentLinks(document)[0].target.toString(), URI.parse(answer.links[0].target).toString());
  h.refresh();
  answer = new Error('A companion file has unsaved changes.');
  const failure = await h.provider.provideTextDocumentContent(document.uri, token());
  assert.match(failure, /proof view unavailable/);
  assert.match(failure, /Save the implementation and its companion files/);
  assert.match(failure, /unsaved changes/);
  assert.equal(failure.includes('new proof text'), false);
  assert.deepEqual(h.links.provideDocumentLinks(document), []);
});

test('invalidation cancels requests and late results cannot replace fresh content or links', async t => {
  const old = deferred();
  let first = true;
  const h = setup(() => first ? (first = false, old.promise) : Promise.resolve(result('fresh proof')));
  t.after(() => h.disposable.dispose());
  const uri = URI.from({ scheme: proofViewScheme, path: '/workspace/source.proof-view',
    query: 'file:///workspace/source.ml' });
  const pending = h.provider.provideTextDocumentContent(uri, token());
  const rejected = assert.rejects(pending, CancellationError);
  h.refresh();
  assert.equal(h.calls[0].token.isCancellationRequested, true);
  assert.equal(await h.provider.provideTextDocumentContent(uri, token()), 'fresh proof');
  old.resolve(result('old proof', 'file:///workspace/old.proof'));
  await rejected;
  assert.equal(await h.provider.provideTextDocumentContent(uri, token()), 'fresh proof');
  assert.equal(h.links.provideDocumentLinks({ uri })[0].target.toString(), URI.parse(result().links[0].target).toString());
});

test('editor cancellation reaches the server and does not cache the cancelled result', async t => {
  const old = deferred();
  const h = setup(() => old.promise);
  t.after(() => h.disposable.dispose());
  const uri = URI.from({ scheme: proofViewScheme, path: '/workspace/source.proof-view',
    query: 'file:///workspace/source.ml' });
  const cancellation = new CancellationTokenSource();
  const pending = h.provider.provideTextDocumentContent(uri, cancellation.token);
  const rejected = assert.rejects(pending, CancellationError);
  cancellation.cancel();
  assert.equal(h.calls[0].token.isCancellationRequested, true);
  old.resolve(result());
  await rejected;
  assert.deepEqual(h.links.provideDocumentLinks({ uri }), []);
});

test('closing a view clears its state and cancels pending requests without reviving it', async t => {
  const old = deferred();
  const h = setup(() => old.promise);
  t.after(() => h.disposable.dispose());
  const uri = URI.from({ scheme: proofViewScheme, path: '/workspace/source.proof-view',
    query: 'file:///workspace/source.ml' });
  const pending = h.provider.provideTextDocumentContent(uri, token());
  const rejected = assert.rejects(pending, CancellationError);
  h.close(uri);
  assert.equal(h.calls[0].token.isCancellationRequested, true);
  old.resolve(result());
  await rejected;
  h.refresh();
  assert.equal(h.changed.length, 0);
  assert.deepEqual(h.links.provideDocumentLinks({ uri }), []);
});
