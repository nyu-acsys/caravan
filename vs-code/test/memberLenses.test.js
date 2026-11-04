const test = require('node:test');
const assert = require('node:assert/strict');
const path = require('node:path');
const { memberLenses } = require('../out/server/memberLenses');
const { parseReport, normalizeMembers } = require('../out/server/report');

const file = path.resolve('members.ml');
function member(id, status, options = {}) {
  const location = { file, start: { line: 2, character: 4 }, end: { line: 2, character: 8 } };
  return { id, name: id, kind: 'function', location, extent: location, group: false,
    status, ownStatus: status, ownChecks: 1, counts: {}, ...options };
}
const titles = (members, state = 'verifying') => memberLenses(members, file, state).map(lens => lens.command.title);

test('source leaves distinguish type checking, trust, proof outcomes, and unfinished checks', () => {
  const statuses = ['unchecked', 'checked', 'trusted', 'verified', 'pending', 'skipped', 'timeout', 'failed'];
  assert.deepEqual(titles(statuses.map((status, index) => member(String(index), status))), [
    '○ not checked', '○ type-checked', '– trusted', '✓ verified', '⋯ checking', '– skipped', '⏱ timed out', '✗ failed'
  ]);
});

test('failed document status preserves independently verified members', () => {
  assert.deepEqual(titles([member('good', 'verified'), member('bad', 'failed')], 'failed'), ['✗ failed', '✓ verified']);
  for (const state of ['verified', 'verifiedWithWarnings']) {
    assert.deepEqual(titles([member('unproved', 'checked')], state), ['○ type-checked']);
  }
});

test('cached results are identified only for current verified members and groups', () => {
  const cached = member('cached', 'verified', { cached: true });
  const fresh = member('fresh', 'verified', { cached: false });
  const group = member('group', 'verified', { cached: true, group: true,
    kind: 'module', counts: { verified: 2 } });
  assert.deepEqual(titles([cached, fresh, group]), [
    '✓ verified (cached)', '✓ verified', '✓ 2 verified (cached)'
  ]);
  assert.deepEqual(titles([cached], 'outdated'), ['○ outdated']);
  assert.deepEqual(titles([cached], 'unavailable'), ['○ unavailable']);
  for (const status of ['unchecked', 'checked', 'trusted', 'pending', 'skipped', 'timeout', 'failed']) {
    assert.ok(titles([member('stale', status, { cached: true })]).every(title => !title.includes('cached')));
  }
});

test('member reports preserve cache provenance and accept older reports without it', () => {
  const location = { file, start_line: 1, start_col: 0, end_line: 1, end_col: 4 };
  const row = { ...location, id: 'f', name: 'f', kind: 'function', extent: location,
    group: false, status: 'verified', own_status: 'verified', own_checks: 1, counts: { verified: 1 } };
  const report = row => JSON.stringify({ errors: [], dependencies: [], annotations: [],
    members: [row], references: [], symbols: [] });
  const normalize = row => normalizeMembers(parseReport(report(row), 0), process.cwd(), () => undefined)[0];
  assert.equal(normalize(row).cached, false);
  assert.equal(normalize({ ...row, cached: true }).cached, true);
  assert.equal(normalize({ ...row, cached: false }).cached, false);
  assert.throws(() => normalize({ ...row, cached: 'true' }), /invalid member status/);
});

test('outdated and unavailable documents do not retain positive result summaries', () => {
  const members = [member('leaf', 'verified'), member('module', 'verified', {
    group: true, kind: 'module', counts: { verified: 3 }
  })];
  assert.deepEqual(titles(members, 'outdated'), ['○ outdated', '○ outdated']);
  assert.deepEqual(titles(members, 'unavailable'), ['○ unavailable', '○ unavailable']);
});

test('module, functor, and proof-module summaries use projected leaf counts once', () => {
  const outer = member('Outer', 'failed', { group: true, kind: 'module', ownChecks: 0,
    counts: { failed: 1, pending: 1, verified: 2 } });
  const inner = member('Outer.Inner', 'pending', { group: true, kind: 'functor', ownChecks: 0,
    parent: 'Outer', counts: { pending: 1, verified: 2 } });
  const proof = member('Proof', 'verified', { group: true, kind: 'proof-module', counts: { verified: 1 } });
  assert.deepEqual(titles([outer, inner, proof]), [
    '✗ 1 failed, 1 checking, 2 verified', '⋯ 1 checking, 2 verified', '✓ 1 verified'
  ]);
});

test('module boundary failures and pending checks remain visible above verified leaves', () => {
  for (const [status, glyph, words] of [['failed', '✗', 'failed'], ['pending', '⋯', 'checking']]) {
    const group = member('M', status, { group: true, kind: 'module', counts: { verified: 3 } });
    assert.deepEqual(titles([group]), [`${glyph} 3 verified, module checks ${words}`]);
  }
  const nested = member('M', 'failed', { group: true, kind: 'module', ownChecks: 0, ownStatus: 'checked', counts: { verified: 3 } });
  assert.deepEqual(titles([nested]), ['✗ 3 verified, module checks failed']);
});

test('unattributed file prerequisites get a lens and identify their effect on groups', () => {
  const root = member('root', 'failed', { kind: 'file', group: true, counts: { verified: 2 } });
  const group = member('M', 'failed', { kind: 'module', group: true, ownChecks: 0, ownStatus: 'verified', counts: { verified: 2 } });
  assert.deepEqual(titles([root, group]), ['✗ 2 verified, file checks failed', '✗ 2 verified, file checks failed']);
  assert.deepEqual(titles([member('root', 'checked', { kind: 'file', group: true, ownChecks: 0 })]), []);
  assert.deepEqual(titles([member('root', 'pending', { kind: 'file', group: true })]), ['⋯ file checks checking']);
});

test('lenses filter files, deduplicate identities, and use source-ordered empty anchors', () => {
  const early = member('early', 'verified', { location: { file,
    start: { line: 1, character: 3 }, end: { line: 1, character: 7 } } });
  const late = member('late', 'pending');
  const foreign = member('foreign', 'failed', { location: { ...late.location, file: path.resolve('other.proof') } });
  const lenses = memberLenses([late, foreign, early, early], file, 'verifying');
  assert.deepEqual(lenses.map(lens => lens.command.title), ['✓ verified', '⋯ checking']);
  assert.deepEqual(lenses.map(lens => lens.range), [early, late].map(value => ({ start: value.location.start, end: value.location.start })));
  for (const lens of lenses) assert.deepEqual(Object.keys(lens.command).sort(), ['command', 'title']);
  assert.ok(lenses.every(lens => lens.command.command === ''));
});
