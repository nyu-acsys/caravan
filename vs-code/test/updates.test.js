const test = require('node:test');
const assert = require('node:assert/strict');
const Module = require('node:module');
const path = require('node:path');
const verifier = require('../out/client/verifier');

const workspacePath = path.resolve('workspace');
const extensionPath = path.resolve('extension');
const storagePath = path.resolve('storage');
let scenario;
const vscode = {
  ConfigurationTarget: { Workspace: 2, Global: 1 },
  ProgressLocation: { Notification: 15 },
  workspace: {
    workspaceFolders: [{ uri: { fsPath: workspacePath } }],
    getConfiguration: () => ({
      get: (key, fallback) => scenario.settings[key] ?? fallback,
      update: async (key, value) => { scenario.settings[key] = value; }
    }),
    getWorkspaceFolder: () => ({ uri: { fsPath: workspacePath } }),
    onDidChangeConfiguration: () => ({ dispose() {} })
  },
  commands: { registerCommand: (name, action) => {
    scenario.commands.set(name, action);
    return { dispose() {} };
  } },
  window: {
    activeTextEditor: { document: { uri: { scheme: 'file', fsPath: path.join(workspacePath, 'main.ml') } } },
    showInformationMessage: async (message, ...actions) => {
      scenario.messages.push({ message, actions });
      return scenario.answers.shift();
    },
    showErrorMessage: async message => { scenario.errors.push(message); },
    withProgress: async (_, action) => action({ report() {} }, {
      isCancellationRequested: false, onCancellationRequested: () => ({ dispose() {} })
    })
  }
};
const core = { ...verifier,
  resolveToolchain: async () => scenario.toolchain,
  platformAsset: () => 'caravan-linux-x64.tar.gz',
  readManifest: async (...args) => {
    scenario.manifestArguments = args;
    return scenario.toolchain.manifest;
  },
  fetchRelease: async () => {
    scenario.fetches++;
    return scenario.fetch ? scenario.fetch() : scenario.release;
  },
  installRelease: async () => {
    scenario.installs++;
    if (scenario.failure) throw new Error(scenario.failure);
    scenario.toolchain = { ...scenario.toolchain, source: 'managed',
      executable: path.join(storagePath, 'verifier', '0.2.0', 'bin', 'caravan'), manifest: scenario.release.manifest };
    return path.join(storagePath, 'verifier', '0.2.0');
  }
};
const load = Module._load;
let VerifierUpdates;
try {
  Module._load = function (request, parent, ...rest) {
    if (request === 'vscode') return vscode;
    if (request === './verifier' && parent.filename.endsWith(`${path.sep}updates.js`)) return core;
    return load.call(this, request, parent, ...rest);
  };
  ({ VerifierUpdates } = require('../out/client/updates'));
} finally { Module._load = load; }

function fixture(settings = {}) {
  const values = new Map();
  const manifest = { version: '0.1.0', lsp_protocol: 1, min_z3: '4.13.0', ocaml_version: '5.5.0', raven_api_version: 1 };
  scenario = { settings, commands: new Map(), messages: [], errors: [], answers: [], fetches: 0, installs: 0,
    toolchain: { source: 'bundled', executable: path.join(extensionPath, 'bundled', 'bin', 'caravan'), arguments: [], manifest },
    release: { tag: 'v0.2.0', manifest: { ...manifest, version: '0.2.0' }, assets: new Map() } };
  const context = { extensionPath, globalStorageUri: { fsPath: storagePath }, subscriptions: [],
    globalState: { get: (key, fallback) => values.get(key) ?? fallback,
      update: async (key, value) => { values.set(key, value); } } };
  const changed = [];
  const manager = new VerifierUpdates(context, { appendLine() {} }, async value => { changed.push(value); });
  return { manager, changed, values };
}

test('update offers respect channels, executable overrides, and daily checks', async () => {
  for (const settings of [{ updateChannel: 'bundled' }, { executable: 'opam' }, { checkForUpdates: false }]) {
    const { manager } = fixture(settings);
    await manager.check(false);
    assert.equal(scenario.fetches, 0);
    manager.dispose();
  }
  const { manager } = fixture();
  scenario.answers.push('Later');
  await manager.check(false);
  await manager.check(false);
  assert.equal(scenario.fetches, 1);
  assert.equal(scenario.installs, 0);
  assert.deepEqual(scenario.messages[0].actions, ['Install', 'Later']);
  manager.dispose();
});

test('accepted update switches selection only after installation succeeds', async () => {
  const { manager, changed } = fixture();
  await manager.refresh();
  scenario.answers.push('Install');
  await manager.check(true);
  assert.equal(scenario.installs, 1);
  assert.equal(changed.length, 2);
  assert.equal(manager.current.source, 'managed');
  assert.equal(manager.current.manifest.version, '0.2.0');
  manager.dispose();
});

test('failed accepted automatic update retains prior selection and reports failure', async () => {
  const { manager, changed } = fixture();
  await manager.refresh();
  scenario.answers.push('Install');
  scenario.failure = 'Checksum mismatch';
  await manager.check(false);
  assert.equal(changed.length, 1);
  assert.equal(manager.current.source, 'bundled');
  assert.match(scenario.errors[0], /Checksum mismatch/);
  manager.dispose();
});

test('selection changes during metadata retrieval suppress obsolete update offers', async () => {
  const { manager } = fixture();
  let complete;
  scenario.fetch = () => new Promise(resolve => { complete = resolve; });
  const pending = manager.check(false);
  while (!complete) await new Promise(resolve => setImmediate(resolve));
  scenario.settings.updateChannel = 'bundled';
  await manager.refresh();
  complete(scenario.release);
  await pending;
  assert.equal(scenario.messages.length, 0);
  assert.equal(scenario.installs, 0);
  manager.dispose();
});

test('incompatible releases explain that the extension needs updating', async () => {
  const { manager } = fixture();
  scenario.fetch = () => Promise.reject(new verifier.CompatibilityError('Update the Caravan extension'));
  await manager.check(false);
  assert.equal(scenario.installs, 0);
  assert.match(scenario.errors[0], /Update the Caravan extension/);
  manager.dispose();
});

test('version command uses the configured launcher arguments and project directory', async () => {
  const { manager } = fixture({ executable: 'opam', arguments: ['exec', '--', 'caravan'], cwd: 'build' });
  manager.register();
  await scenario.commands.get('caravan.showVerifierVersion')();
  assert.deepEqual(scenario.manifestArguments, ['opam', undefined, ['exec', '--', 'caravan'], path.join(workspacePath, 'build')]);
  assert.match(scenario.messages[0].message, /Caravan 0.1.0 \(configured\)/);
  manager.dispose();
});
