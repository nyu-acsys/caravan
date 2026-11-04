const test = require('node:test');
const assert = require('node:assert/strict');
const Module = require('node:module');
const { openContractCommand } = require('../out/shared/protocol');

let action;
const opened = [];
const vscode = {
  commands: { registerCommand: (name, callback) => {
    assert.equal(name, openContractCommand);
    action = callback;
    return { dispose() {} };
  } },
  Uri: { parse: value => ({ scheme: value.split(':')[0], toString: () => value }) },
  Range: class { constructor(startLine, startCharacter, endLine, endCharacter) {
    this.start = { line: startLine, character: startCharacter };
    this.end = { line: endLine, character: endCharacter };
  } },
  window: { showTextDocument: async (uri, options) => { opened.push({ uri: uri.toString(), options }); } }
};
const load = Module._load;
let registerContractNavigation;
try {
  Module._load = function (request, ...rest) {
    return request === 'vscode' ? vscode : load.call(this, request, ...rest);
  };
  ({ registerContractNavigation } = require('../out/client/contracts'));
} finally { Module._load = load; }

test('contract lens navigation opens the exact companion source range', async () => {
  registerContractNavigation();
  const source = { uri: 'file:///workspace/stack%20contract.mli',
    range: { start: { line: 4, character: 7 }, end: { line: 7, character: 12 } } };
  await action(source);
  assert.equal(opened.length, 1);
  assert.equal(opened[0].uri, source.uri);
  assert.deepEqual(opened[0].options.selection.start, source.range.start);
  assert.deepEqual(opened[0].options.selection.end, source.range.end);
  assert.equal(opened[0].options.preview, true);
});

test('malformed or non-file contract navigation does not open an editor', async () => {
  registerContractNavigation();
  const count = opened.length;
  const valid = { start: { line: 0, character: 0 }, end: { line: 1, character: 0 } };
  for (const value of [undefined, null, {}, { uri: 'command:unexpected', range: valid },
    { uri: 'file:///workspace/a.mli', range: { ...valid, start: { line: -1, character: 0 } } },
    { uri: 'file:///workspace/a.mli', range: { ...valid, end: { line: 0, character: -1 } } }]) {
    await action(value);
  }
  assert.equal(opened.length, count);
});
