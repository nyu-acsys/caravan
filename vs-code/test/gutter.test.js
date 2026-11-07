const test = require('node:test');
const assert = require('node:assert/strict');
const Module = require('node:module');

const vscode = { DiagnosticSeverity: { Error: 0, Warning: 1, Information: 2 } };
const load = Module._load;
let gutterMarkers;
try {
  Module._load = function (request, ...rest) {
    return request === 'vscode' ? vscode : load.call(this, request, ...rest);
  };
  ({ gutterMarkers } = require('../out/client/gutter'));
} finally { Module._load = load; }

const uri = value => ({ toString: () => value });
const range = line => ({ start: { line, character: 2 } });
const diagnostic = (line, severity, message, relatedInformation = []) => ({
  source: 'Caravan', range: range(line), severity, message, relatedInformation
});

test('gutter markers include cross-file related locations and choose the strongest marker per line', () => {
  const source = uri('file:///main.ml');
  const proof = uri('file:///main.proof');
  const related = { location: { uri: proof, range: range(3) }, message: 'Specification origin' };
  const entries = [
    [source, [diagnostic(1, 0, 'Failed assertion', [related]),
      diagnostic(2, 1, 'Trusted contract'), diagnostic(3, 0, 'Primary failure')]],
    [proof, [diagnostic(3, 1, 'Proof warning'), diagnostic(4, 2, 'Information')]],
    [source, [{ ...diagnostic(5, 0, 'Other extension'), source: 'Other' }]]
  ];
  const main = gutterMarkers(source, entries);
  assert.deepEqual([...main.errors], [[1, ['Failed assertion']], [3, ['Primary failure']]]);
  assert.deepEqual([...main.warnings], [[2, ['Trusted contract']]]);
  assert.deepEqual([...main.related], []);
  const companion = gutterMarkers(proof, entries);
  assert.deepEqual([...companion.errors], []);
  assert.deepEqual([...companion.warnings], [[3, ['Specification origin', 'Proof warning']]]);
  assert.deepEqual([...companion.related], []);
});

test('related locations receive a marker without a primary diagnostic in their file', () => {
  const source = uri('file:///main.ml');
  const proof = uri('file:///main.proof');
  const related = { location: { uri: proof, range: range(8) }, message: 'Inherited contract' };
  const result = gutterMarkers(proof, [[source, [diagnostic(2, 0, 'Failed', [related, related])]]]);
  assert.deepEqual([...result.related], [[8, ['Inherited contract']]]);
});
