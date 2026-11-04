const test = require('node:test');
const assert = require('node:assert/strict');
const path = require('node:path');
const { URI } = require('vscode-uri');
const { renderProofView } = require('../out/server/proofView');

const workspace = path.resolve('workspace');
const root = path.join(workspace, 'queue.ml');
const location = (file, line, start, end = start) => ({ file,
  start: { line, character: start }, end: { line, character: end } });
const source = '(* 🙂 *)\r\nlet create () = Atomic.make []\r\n';
const contractText = '(*@ t = create () ensures stack t [] *)';
const contractFile = root.replace(/\.ml$/, '.mli');
const proofFile = root.replace(/\.ml$/, '.proof');
const companions = new Map([[contractFile, `val create : unit -> t\n${contractText}\n`],
  [proofFile, 'predicate stack t xs = own t xs\nproof create = on return fold stack t []\n']]);
const contract = { source: 'create', location: location(root, 1, 4, 10),
  sourceLocation: location(contractFile, 1, 0, contractText.length), clauses: [] };
const step = { location: location(root, 1, source.split('\n')[1].trimEnd().length),
  sourceLocation: location(proofFile, 1, 25, 40), text: 'proof fold stack t []' };

test('proof view interleaves authoritative attachments, retains context, and maps source links', () => {
  const rendered = renderProofView(root, source, { contracts: [contract, contract], steps: [step, step] },
    file => companions.get(file), workspace);
  assert.equal((rendered.text.match(/Contract for create from/g) ?? []).length, 1);
  assert.equal((rendered.text.match(/Proof step from/g) ?? []).length, 1);
  assert.ok(rendered.text.includes('(*@ t = create () ensures stack t [] *)'));
  assert.ok(rendered.text.includes('let create () = Atomic.make []\n(* Proof step from'));
  assert.ok(rendered.text.includes('(*@ proof fold stack t [] *)'));
  assert.ok(rendered.text.includes(companions.get(proofFile)));
  assert.ok(rendered.text.includes(companions.get(contractFile)));
  assert.ok(rendered.text.includes('(* 🙂 *)\r\n'));
  const lines = rendered.text.split('\n');
  for (const link of rendered.links) {
    assert.equal(link.range.start.line, link.range.end.line);
    const label = lines[link.range.start.line].slice(link.range.start.character, link.range.end.character);
    assert.match(label, /^"queue\.(ml|mli|proof):\d+"$/);
    assert.equal(URI.parse(link.target).scheme, 'file');
  }
  assert.ok(rendered.links.some(link => URI.parse(link.target).fragment === 'L2,26'));
});

test('proof view keeps inline annotations and rejects invalid locations', () => {
  const inline = 'let f () = 0 (*@ assert true *)\n';
  const rendered = renderProofView(root, inline, { contracts: [], steps: [] }, () => undefined, workspace);
  assert.ok(rendered.text.includes(inline));
  assert.equal(rendered.links.length, 1);
  assert.throws(() => renderProofView(root, inline, { contracts: [], steps: [{ ...step,
    location: location(root, 12, 0) }] }, () => undefined, workspace), /outside the saved implementation/);
  const other = { ...step, location: location(path.join(workspace, 'other.ml'), 0, 0) };
  assert.equal(renderProofView(root, inline, { contracts: [], steps: [other] }, () => undefined, workspace).text.includes('Proof step from'), false);
});
