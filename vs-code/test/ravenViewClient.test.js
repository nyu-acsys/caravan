const test = require('node:test');
const assert = require('node:assert/strict');
const { URI } = require('vscode-uri');
const { ravenViewScheme } = require('../out/shared/protocol');
const { setup, token, deferred, CancellationError } = require('./readOnlyViewHarness');

const harness = (request, language = 'raven') =>
  setup(request ?? (async () => ({ text: 'proc main() {}' })), 'Raven', language);

test('Raven views use a readonly provider, Raven file associations, and native companion URIs', async t => {
  const h = harness();
  t.after(() => h.disposable.dispose());
  assert.deepEqual(h.registrations, [{ kind: 'content', scheme: ravenViewScheme }]);
  for (const source of [
    URI.from({ scheme: 'file', path: '/workspace/λ # contract.ml' }),
    URI.from({ scheme: 'file', path: '/workspace/λ # contract.mli' }),
    URI.from({ scheme: 'file', path: '/C:/Users/Test #/λ.proof' }),
    URI.from({ scheme: 'file', authority: 'server', path: '/share/Test #/λ.mli' })
  ]) {
    await h.show({ uri: source, isDirty: false });
    const { document, options } = h.opened.at(-1);
    const expected = source.with({ path: source.path.replace(/\.(ml|mli|proof)$/, '.ml') });
    assert.equal(h.calls.at(-1).uri, expected.toString());
    assert.equal(URI.parse(document.uri.toString()).query, expected.toString());
    assert.equal(document.uri.path.endsWith('.rav'), true);
    assert.equal(document.languageId, 'raven');
    assert.deepEqual(options, { viewColumn: -2, preview: true });
    h.close(document.uri);
    await h.provider.provideTextDocumentContent(URI.parse(document.uri.toString()), token());
    assert.equal(h.calls.at(-1).uri, expected.toString());
    h.close(document.uri);
  }
});

test('Raven views remain usable as plain text without a Raven language provider', async t => {
  const h = harness(undefined, 'plaintext');
  t.after(() => h.disposable.dispose());
  await h.show('file:///workspace/source.ml');
  assert.equal(h.opened[0].document.languageId, 'plaintext');
  assert.equal(h.opened[0].document.text, 'proc main() {}');
});

test('Raven view rejects dirty sources and refreshes from the generated editor', async t => {
  let answer = { text: 'old translation' };
  const h = harness(async () => {
    if (answer instanceof Error) throw answer;
    return answer;
  });
  t.after(() => h.disposable.dispose());
  await h.show({ uri: URI.parse('file:///workspace/source.proof'), isDirty: true });
  await h.show('untitled:source.ml');
  assert.equal(h.calls.length, 0);
  assert.match(h.messages[0], /Save the file/);
  await h.show('file:///workspace/source.ml');
  const document = h.opened[0].document;
  answer = { text: 'new translation' };
  await h.show({ uri: document.uri, isDirty: false });
  await h.refreshed();
  assert.equal(document.text, 'new translation');
  answer = new Error('Companion has unsaved changes. */ unsafe');
  h.refresh();
  await h.refreshed();
  assert.match(document.text, /^\/\* Caravan Raven view unavailable/);
  assert.match(document.text, /unsaved changes/);
  assert.equal(document.text.includes('new translation'), false);
  assert.equal(document.text.includes('*/ unsafe'), false);
});

test('Raven refresh cancels pending translations and prevents stale content', async t => {
  const old = deferred();
  let first = true;
  const h = harness(() => first ? (first = false, old.promise) : Promise.resolve({ text: 'fresh Raven' }));
  t.after(() => h.disposable.dispose());
  const uri = URI.from({ scheme: ravenViewScheme, path: '/workspace/source.rav', query: 'file:///workspace/source.ml' });
  const pending = h.provider.provideTextDocumentContent(uri, token());
  const rejected = assert.rejects(pending, CancellationError);
  h.refresh();
  assert.equal(h.calls[0].token.isCancellationRequested, true);
  assert.equal(await h.provider.provideTextDocumentContent(uri, token()), 'fresh Raven');
  old.resolve({ text: 'stale Raven' });
  await rejected;
  assert.equal(await h.provider.provideTextDocumentContent(uri, token()), 'fresh Raven');
});

test('closing a Raven view cancels work and removes its refresh subscription state', async t => {
  const old = deferred();
  const h = harness(() => old.promise);
  t.after(() => h.disposable.dispose());
  const uri = URI.from({ scheme: ravenViewScheme, path: '/workspace/source.rav', query: 'file:///workspace/source.ml' });
  const pending = h.provider.provideTextDocumentContent(uri, token());
  const rejected = assert.rejects(pending, CancellationError);
  h.close(uri);
  assert.equal(h.calls[0].token.isCancellationRequested, true);
  old.resolve({ text: 'late translation' });
  await rejected;
  h.refresh();
  assert.deepEqual(h.changed, []);
});
