const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const os = require('node:os');
const path = require('node:path');
const http = require('node:http');
const { promisify } = require('node:util');
const { execFile } = require('node:child_process');
const core = require('../out/client/verifier');
const { systemPath } = require('../out/shared/toolchain');
const run = promisify(execFile);

test('native release installs and verifies Saturn with its relocated compiler and solver',
  { skip: !process.env.CARAVAN_TEST_RELEASE_DIRECTORY, timeout: 180000 }, async () => {
    const directory = process.env.CARAVAN_TEST_RELEASE_DIRECTORY;
    const asset = core.platformAsset();
    assert.ok(asset);
    const names = ['manifest.json', 'SHA256SUMS', asset];
    const contents = new Map(await Promise.all(names.map(async name => [name, await fs.readFile(path.join(directory, name))])));
    const server = http.createServer((request, response) => {
      const content = contents.get(request.url.slice(1));
      response.writeHead(content ? 200 : 404);
      response.end(content);
    });
    await new Promise(resolve => server.listen(0, '127.0.0.1', resolve));
    const storage = await fs.mkdtemp(path.join(os.tmpdir(), 'caravan-native-install-'));
    try {
      const base = `http://127.0.0.1:${server.address().port}`;
      const manifest = JSON.parse(contents.get('manifest.json'));
      const release = { tag: `v${manifest.version}`, manifest,
        assets: new Map(names.map(name => [name, `${base}/${name}`])) };
      const root = await core.installRelease(release, storage, { allowHttpForTests: true });
      const selected = await core.resolveToolchain({ extensionPath: storage, storagePath: storage, channel: 'stable' });
      assert.equal(selected.source, 'managed');
      assert.equal(selected.bundleRoot, root);
      const repository = path.resolve(__dirname, '../..');
      const baseEnvironment = { ...process.env };
      // Preserve SystemRoot and other OS variables while excluding developer toolchains.
      for (const key of Object.keys(baseEnvironment)) {
        if (['PATH', 'OCAMLLIB', 'CAML_LD_LIBRARY_PATH'].includes(key.toUpperCase())) delete baseEnvironment[key];
      }
      baseEnvironment.PATH = systemPath(process.env);
      baseEnvironment.OCAMLLIB = path.join(storage, 'missing-original-compiler');
      const environment = core.toolchainEnvironment(root, baseEnvironment);
      assert.equal(selected.executable, path.join(root, 'bin', process.platform === 'win32' ? 'caravan.exe' : 'caravan'));
      assert.ok(environment.PATH.startsWith(path.join(root, 'bin') + path.delimiter));
      if (process.platform === 'win32') {
        assert.deepEqual(Object.keys(environment).filter(key => key.toUpperCase() === 'PATH'), ['PATH']);
        await fs.access(path.join(root, 'bin', 'z3.exe'));
      }
      const result = await run(selected.executable, ['--shh', '-I', path.join(repository, 'test/saturn/backoff'),
        path.join(repository, 'test/saturn/treiber_stack/treiber_stack.ml')], { env: environment, timeout: 120000 });
      assert.match(result.stdout, /Verification successful/);
    } finally {
      await new Promise(resolve => server.close(resolve));
      await fs.rm(storage, { recursive: true, force: true });
    }
  });
