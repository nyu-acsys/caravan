const test = require('node:test');
const assert = require('node:assert/strict');
const path = require('node:path');
const { contractLenses } = require('../out/server/contracts');

const root = path.resolve('module.ml');
function contract(clauses) {
  return { location: { file: root, start: { line: 2, character: 4 }, end: { line: 2, character: 5 } },
    source: 'f', sourceLocation: { file: path.resolve('module.mli'),
      start: { line: 3, character: 0 }, end: { line: 4, character: 9 } },
    clauses: clauses.map(text => ({ keyword: 'ensures', text })) };
}

test('contract summaries remain readable for header-only and long Unicode contracts', () => {
  assert.equal(contractLenses([contract([])], root)[0].command.title, 'contract (module.mli)');
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
