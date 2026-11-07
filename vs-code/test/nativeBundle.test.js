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
const { parseReport, normalizeContracts, normalizeProofSteps, normalizeMembers } = require('../out/server/report');
const { VerificationProcesses } = require('../out/server/verificationProcesses');
const { memberLenses } = require('../out/server/memberLenses');
const { contractHover } = require('../out/server/contracts');
const { renderProofView } = require('../out/server/proofView');
const { proofHints } = require('../out/server/proofHints');
const { readFileSync } = require('node:fs');
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
      assert.equal(contents.get('manifest.json').toString('utf8'), JSON.stringify(manifest, null, 2) + '\n',
        'Release manifests must use identical UTF-8 and LF formatting on every platform');
      const release = { tag: `v${manifest.version}`, manifest,
        assets: new Map(names.map(name => [name, `${base}/${name}`])) };
      const root = await core.installRelease(release, storage, { allowHttpForTests: true });
      assert.deepEqual(await fs.readFile(path.join(root, 'manifest.json')), contents.get('manifest.json'));
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
      const source = path.join(repository, 'test/saturn/treiber_stack/treiber_stack.ml');
      const includes = ['-I', path.join(repository, 'test/saturn/backoff')];
      const metadata = await run(selected.executable,
        ['--lsp-mode', '--lsp-annotations', '--lsp-annotations-only', ...includes, source],
        { env: environment, timeout: 30000 });
      const report = parseReport(metadata.stdout, 0);
      const contracts = normalizeContracts(report, repository, file => readFileSync(file, 'utf8'));
      const hover = contractHover(contracts, source, contracts[0].location.start,
        file => readFileSync(file, 'utf8'), repository);
      assert.ok(hover.contents.value.includes('Contract from [test/saturn/treiber\\_stack/treiber\\_stack.mli:'));
      assert.match(hover.contents.value, /```caravan-proof\nt = create \(\)/);
      assert.equal(hover.contents.value.includes('(*@'), false);
      const steps = normalizeProofSteps(report, repository, file => readFileSync(file, 'utf8'));
      assert.ok(steps.length > 0);
      const hints = proofHints(steps, source, { start: { line: 0, character: 0 },
        end: { line: readFileSync(source, 'utf8').split('\n').length, character: 0 } }, repository);
      assert.equal(hints.length, steps.length);
      assert.ok(hints.some(hint => hint.label[0].value === 'fold stack t []'));
      assert.ok(hints.every(hint => hint.label[0].location.uri.endsWith('/treiber_stack.proof')));
      const view = renderProofView(source, readFileSync(source, 'utf8'), { contracts, steps },
        file => { try { return readFileSync(file, 'utf8'); } catch { return undefined; } }, repository);
      assert.ok(view.text.includes('(*@ proof fold stack t [] *)'));
      assert.ok(view.text.includes('predicate stack'));
      assert.ok(view.links.some(link => link.target.includes('/treiber_stack.proof#')));
      const phases = [];
      const snapshots = [];
      const verificationArgs = ['--lsp-mode', '--lsp-annotations', '--cache-dir',
        path.join(storage, 'verification-cache'), ...includes, source];
      const result = await new VerificationProcesses(1).serve(selected.executable, [],
        verificationArgs, repository,
        new AbortController().signal, environment, (stdout, phase) => {
          phases.push(phase);
          snapshots.push(normalizeMembers(parseReport(stdout), repository,
            file => readFileSync(file, 'utf8')));
        });
      assert.equal(result.code, 0, result.stderr);
      assert.equal(phases[0], 'typed');
      assert.ok(phases.includes('scheduled'));
      assert.ok(phases.includes('progress'));
      assert.ok(snapshots.some(members => members.some(member => member.status === 'pending')));
      const verified = normalizeMembers(parseReport(result.stdout, result.code), repository,
        file => readFileSync(file, 'utf8'));
      assert.ok(verified.some(member => member.name === 'create' && member.status === 'verified'));
      assert.ok(memberLenses(verified, source, 'verified').length >= 6);
      const reused = await new VerificationProcesses(1).serve(selected.executable, [],
        verificationArgs, repository, new AbortController().signal, environment, () => {});
      assert.equal(reused.code, 0, reused.stderr);
      const cached = normalizeMembers(parseReport(reused.stdout, reused.code), repository,
        file => readFileSync(file, 'utf8'));
      assert.ok(cached.some(member => member.name === 'create' && member.cached));
      assert.ok(memberLenses(cached, source, 'verified').some(lens => lens.command.title.includes('(cached)')));
    } finally {
      await new Promise(resolve => server.close(resolve));
      await fs.rm(storage, { recursive: true, force: true });
    }
  });
