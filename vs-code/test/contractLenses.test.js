const test = require('node:test');
const assert = require('node:assert/strict');
const path = require('node:path');
const { contractLenses, contractHover } = require('../out/server/contracts');

const root = path.resolve('module.ml');
function contract(clauses) {
  return { location: { file: root, start: { line: 2, character: 4 }, end: { line: 2, character: 5 } },
    source: 'f', sourceLocation: { file: path.resolve('module.mli'),
      start: { line: 3, character: 0 }, end: { line: 4, character: 9 } },
    clauses: clauses.map(text => ({ keyword: 'ensures', text })) };
}

test('contract summaries remain readable for header-only and long Unicode contracts', () => {
  assert.equal(contractLenses([contract([])], root)[0].command.title, 'contract');
  const title = contractLenses([contract(['🙂'.repeat(150) + '\nfalse'])], root)[0].command.title;
  assert.ok(title.endsWith('…'));
  assert.ok(title.isWellFormed());
  assert.equal(title.includes('\n'), false);
});

test('duplicate generated workers produce one lens at the original implementation', () => {
  const original = contract(['true']);
  const result = contractLenses([original, original, { ...original,
    location: { ...original.location, file: path.resolve('other.ml') } }], root);
  assert.equal(result.length, 1);
});

test('contract hovers omit outer comment markers, preserve the contract, and link its location', () => {
  const original = contract(['fallback']);
  const body = '(*@ result = f specified\n    requires specified > 0\n    ensures ' + '🙂'.repeat(150) + ' *)';
  original.sourceLocation = { file: path.resolve('nested/module.mli'),
    start: { line: 1, character: 3 }, end: { line: 3, character: body.split('\n')[2].length } };
  const text = `val f : int -> int\n   ${body}\n`;
  const hover = contractHover([original], root, { line: 2, character: 4 }, () => text, path.dirname(root));
  assert.deepEqual(hover.range, { start: original.location.start, end: original.location.end });
  assert.ok(hover.contents.value.includes('nested/module.mli:2'));
  assert.ok(hover.contents.value.includes('#L2%2C4>'));
  assert.ok(hover.contents.value.includes(body.slice(3, -2).trim()));
  assert.equal(hover.contents.value.includes('(*@'), false);
  assert.equal(hover.contents.value.includes('*)'), false);
  for (const position of [{ line: 2, character: 3 }, { line: 2, character: 5 }, { line: 3, character: 4 }]) {
    assert.equal(contractHover([original], root, position, () => text, path.dirname(root)), null);
  }
  assert.equal(contractHover([original], path.resolve('other.ml'), { line: 2, character: 4 }, () => text, path.dirname(root)), null);
});

test('proof contract hovers escape Markdown and fall back to clauses when source is unavailable', () => {
  const original = contract(['a ``` fence']);
  original.sourceLocation.file = path.resolve('proof [name].proof');
  const hover = contractHover([original], root, { line: 2, character: 4 }, () => undefined, path.dirname(root));
  assert.ok(hover.contents.value.includes('proof \\[name\\].proof:4'));
  assert.ok(hover.contents.value.includes('````caravan-proof\nensures a ``` fence\n````'));
  assert.ok(hover.contents.value.includes('proof%20%5Bname%5D.proof#L4%2C1'));
});
