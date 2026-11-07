const test = require('node:test');
const assert = require('node:assert/strict');
const path = require('node:path');
const { URI } = require('vscode-uri');
const { proofHints } = require('../out/server/proofHints');

const root = path.resolve('queue.ml');
const workspace = path.dirname(root);
const range = { start: { line: 0, character: 0 }, end: { line: 20, character: 0 } };
const step = (text, line = 3, character = 8) => ({ text,
  location: { file: root, start: { line, character }, end: { line, character } },
  sourceLocation: { file: path.resolve('proof [source].proof'),
    start: { line: 7, character: 4 }, end: { line: 8, character: 12 } } });

test('proof hints show short directives and link exact original proof ranges', () => {
  const original = step('proof fold stack t []');
  const [hint] = proofHints([original], root, range, workspace);
  assert.equal(hint.label[0].value, 'fold stack t []');
  assert.deepEqual(hint.position, original.location.start);
  assert.deepEqual(hint.label[0].location, {
    uri: URI.file(original.sourceLocation.file).toString(),
    range: { start: original.sourceLocation.start, end: original.sourceLocation.end }
  });
  assert.equal(hint.tooltip.kind, 'markdown');
  assert.ok(hint.tooltip.value.includes('Proof step from [proof \\[source\\].proof:8]'));
  assert.ok(hint.tooltip.value.includes('```caravan-proof\nproof fold stack t []\n```'));
});

test('long annotations remain compact while hovers retain full text and safe Markdown', () => {
  for (const text of ['Ghost.scope (fun step ->\n' + '🙂'.repeat(100) + '\nstep ())',
    'proof begin\nassert true;\nlemma some_fact ()\nend', 'assert "' + '🙂'.repeat(100) + ' ```"']) {
    const [hint] = proofHints([step(text)], root, range, workspace);
    assert.ok(Array.from(hint.label[0].value).length <= 64);
    assert.equal(hint.label[0].value.includes('\n'), false);
    assert.ok(hint.label[0].value.isWellFormed());
    assert.ok(hint.tooltip.value.includes(text));
    if (text.includes('```')) assert.ok(hint.tooltip.value.includes('````caravan-proof'));
  }
});

test('proof hints respect requested ranges, avoid duplicates and inline annotations, and sort by position', () => {
  const first = step('commit', 3, 8);
  const second = step('returning [] -> commit', 5, 12);
  const candidates = [second, first, first,
    { ...first, location: { ...first.location, file: path.resolve('other.ml') } },
    { ...first, sourceLocation: { ...first.sourceLocation, file: root } }];
  assert.deepEqual(proofHints(candidates, root, range, workspace).map(hint => hint.label[0].value),
    ['commit', 'returning [] -> commit']);
  assert.deepEqual(proofHints(candidates, root,
    { start: { line: 3, character: 9 }, end: { line: 5, character: 12 } }, workspace).map(hint => hint.label[0].value),
    ['returning [] -> commit']);
});
