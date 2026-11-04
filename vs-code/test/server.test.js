const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const os = require('node:os');
const path = require('node:path');
const { URI } = require('vscode-uri');
const { spawn } = require('node:child_process');
const { parseReport, normalizeReport, utf16Column } = require('../out/server/report');
const { VerificationProcesses } = require('../out/server/verificationProcesses');

const delay = ms => new Promise(resolve => setTimeout(resolve, ms));
const uri = file => URI.file(file).toString();
const fakeVerifier = `
const fs = require('node:fs');
const path = require('node:path');
const file = process.argv.at(-1);
const text = fs.readFileSync(file, 'utf8');
fs.appendFileSync(path.join(path.dirname(file), 'runs'), JSON.stringify(process.argv.slice(2)) + '\\n');
fs.writeFileSync(path.join(path.dirname(file), 'environment'), JSON.stringify({OCAMLLIB:process.env.OCAMLLIB,PATH:process.env.PATH}));
const location = {file,start_line:1,start_col:text.includes('unicode')?6:2,end_line:1,end_col:text.includes('unicode')?10:4};
const fail = text.includes('fail');
const warning = text.includes('warning');
const report = {errors:fail?[
 {...location,kind:'Verification',message:['Failed assertion']},
 {...location,file:file.replace(/\\.ml$/,'.proof'),start_col:2,end_col:text.includes('unicode')?6:4,kind:'RelatedLoc',message:['Related specification']}
]:warning?[{...location,kind:'Warning',message:['Trusted specification']}]:[],
 dependencies:[file,path.join(path.dirname(file),'dependency.ml')],annotations:[],members:[],references:[],symbols:[]};
if(text.includes('nodeps')) report.dependencies=[];
function answer() {
 if(text.includes('stderr')) {console.error('solver could not start');process.exit(2);}
 if(text.includes('malformed')) process.stdout.write('bad JSON');
 else if(text.includes('empty')) process.stdout.write('');
 else process.stdout.write(JSON.stringify(report));
 process.exit(text.includes('exitbad')?0:fail?1:0);
}
if(text.includes('slow')) setTimeout(answer,1200); else answer();
`;

async function fixture(t, initial = 'let x = 1', toolchain) {
	const dir = URI.file(await fs.mkdtemp(path.join(os.tmpdir(), 'caravan lsp '))).fsPath;
	const file = path.join(dir, 'main.ml');
	const script = path.join(dir, 'fake verifier.cjs');
	await fs.writeFile(file, initial);
	await fs.writeFile(script, fakeVerifier);
	const settings = { executable: process.execPath, arguments: [script], includePaths: ['include with spaces'], smtTimeout: 77, verifyOnSave: true };
	const child = spawn(process.execPath, [path.resolve(__dirname, '../out/server/server.js'), '--stdio'], { stdio: ['pipe', 'pipe', 'pipe'] });
	const messages = [];
	const pending = new Map();
	let buffer = Buffer.alloc(0);
	let nextId = 0;
	let stderr = '';
	child.stderr.on('data', data => { stderr += data; });
	const send = message => {
		const data = Buffer.from(JSON.stringify({ jsonrpc: '2.0', ...message }));
		child.stdin.write(`Content-Length: ${data.length}\r\n\r\n`);
		child.stdin.write(data);
	};
	child.stdout.on('data', data => {
		buffer = Buffer.concat([buffer, data]);
		while (true) {
			const headerEnd = buffer.indexOf('\r\n\r\n');
			if (headerEnd < 0) break;
			const length = Number(/Content-Length: (\d+)/i.exec(buffer.subarray(0, headerEnd).toString())[1]);
			if (buffer.length < headerEnd + 4 + length) break;
			const message = JSON.parse(buffer.subarray(headerEnd + 4, headerEnd + 4 + length).toString());
			buffer = buffer.subarray(headerEnd + 4 + length);
			if (message.method && message.id !== undefined) {
				send({ id: message.id, result: message.method === 'workspace/configuration' ? message.params.items.map(() => settings) : null });
			} else if (message.id !== undefined) {
				const callback = pending.get(message.id);
				pending.delete(message.id);
				callback?.(message);
			} else messages.push(message);
		}
	});
	const request = (method, params) => new Promise((resolve, reject) => {
		const id = nextId++;
		const timer = setTimeout(() => reject(new Error(`Timed out ${method}: ${stderr}`)), 5000);
		pending.set(id, response => { clearTimeout(timer); response.error ? reject(new Error(JSON.stringify(response.error))) : resolve(response.result); });
		send({ id, method, params });
	});
	const notify = (method, params) => send({ method, params });
	const wait = async (predicate, from = 0) => {
		const deadline = Date.now() + 5000;
		while (Date.now() < deadline) {
			const found = messages.slice(from).find(predicate);
			if (found) return found;
			if (child.exitCode !== null) throw new Error(`Server exited ${child.exitCode}: ${stderr}`);
			await delay(10);
		}
		throw new Error(`Timed out waiting for message: ${JSON.stringify(messages.slice(from))}; ${stderr}`);
	};
	const state = (value, from = 0, target = file) => wait(message => message.method === 'caravan/verificationState' && message.params.uri === uri(target) && message.params.state === value, from);
	const open = async (target = file, version = 1) => notify('textDocument/didOpen', { textDocument: { uri: uri(target), languageId: target.endsWith('.proof') ? 'caravan-proof' : 'ocaml', version, text: await fs.readFile(target, 'utf8') } });
	t.after(async () => {
		if (child.exitCode === null) {
			try { await request('shutdown', null); notify('exit'); } catch { child.kill('SIGTERM'); }
			await Promise.race([new Promise(resolve => child.once('exit', resolve)), delay(1000)]);
			if (child.exitCode === null) child.kill('SIGKILL');
		}
		await fs.rm(dir, { recursive: true, force: true });
	});
	await request('initialize', { processId: process.pid, rootUri: uri(dir), workspaceFolders: [{ uri: uri(dir), name: 'test' }], capabilities: { workspace: { configuration: true } }, initializationOptions: { toolchain } });
	notify('initialized', {});
	return { dir, file, settings, messages, notify, wait, state, open };
}

test('save and manual verification resolve companions, flags and related diagnostics', { timeout: 15000 }, async t => {
	const f = await fixture(t, 'let x = fail');
	const proof = f.file.replace(/\.ml$/, '.proof');
	await fs.writeFile(proof, 'proof');
	await f.open();
	await f.state('unchecked');
	await delay(60);
	await assert.rejects(fs.readFile(path.join(f.dir, 'runs')), { code: 'ENOENT' });
	f.notify('textDocument/didSave', { textDocument: { uri: uri(f.file) } });
	await f.state('failed');
	const publication = await f.wait(message => message.method === 'textDocument/publishDiagnostics' && message.params.diagnostics.length > 0);
	assert.deepEqual(publication.params.diagnostics[0].range, { start: { line: 0, character: 2 }, end: { line: 0, character: 4 } });
	assert.equal(publication.params.diagnostics[0].relatedInformation[0].location.uri, uri(proof));
	const args = JSON.parse((await fs.readFile(path.join(f.dir, 'runs'), 'utf8')).trim());
	assert.deepEqual(args, ['--lsp-mode', '--lsp-annotations', '--smt-timeout', '77', '-I', path.join(f.dir, 'include with spaces'), f.file]);
	await f.open(proof);
	await f.state('failed', 0, proof);
	const from = f.messages.length;
	f.notify('caravan/verify', { uri: uri(proof) });
	await f.state('failed', from, proof);
	assert.equal((await fs.readFile(path.join(f.dir, 'runs'), 'utf8')).trim().split('\n').length, 2);
});

test('dirty buffers and dependency edits invalidate results and cancel stale runs', { timeout: 15000 }, async t => {
	const f = await fixture(t, 'slow');
	const dependency = path.join(f.dir, 'dependency.ml');
	await fs.writeFile(dependency, 'let dependency = 0');
	await f.open();
	f.notify('caravan/verify', { uri: uri(f.file) });
	await f.state('verifying');
	const from = f.messages.length;
	f.notify('textDocument/didChange', { textDocument: { uri: uri(f.file), version: 2 }, contentChanges: [{ text: 'let x = 2' }] });
	await f.state('outdated', from);
	f.notify('caravan/verify', { uri: uri(f.file) });
	await f.wait(message => message.method === 'caravan/verificationState' && message.params.message?.includes('Save changed'), from);
	await delay(1300);
	assert.equal(f.messages.slice(from).some(message => message.params?.state === 'verified'), false);
	await fs.writeFile(f.file, 'let x = 2');
	f.notify('textDocument/didSave', { textDocument: { uri: uri(f.file) } });
	await f.state('verified', from);
	await f.open(dependency);
	const changed = f.messages.length;
	f.notify('textDocument/didChange', { textDocument: { uri: uri(dependency), version: 2 }, contentChanges: [{ text: 'let dependency = 1' }] });
	await f.state('outdated', changed);
	assert.ok(f.messages.slice(changed).some(message => message.method === 'textDocument/publishDiagnostics' && message.params.uri === uri(f.file) && message.params.diagnostics.length === 0));
});

test('missing implementation, missing executable, malformed reports and stderr remain unavailable', { timeout: 15000 }, async t => {
	const f = await fixture(t);
	const proof = path.join(f.dir, 'missing.proof');
	await fs.writeFile(proof, 'proof');
	await f.open(proof);
	f.notify('caravan/verify', { uri: uri(proof) });
	await f.state('unavailable', 0, proof);
	await f.open();
	f.settings.verifyOnSave = false;
	let version = 1;
	for (const content of ['malformed', 'empty', 'nodeps', 'fail exitbad', 'stderr']) {
		await fs.writeFile(f.file, content);
		f.notify('textDocument/didChange', { textDocument: { uri: uri(f.file), version: ++version }, contentChanges: [{ text: content }] });
		f.notify('textDocument/didSave', { textDocument: { uri: uri(f.file) } });
		const from = f.messages.length;
		f.notify('caravan/verify', { uri: uri(f.file) });
		const failure = await f.state('unavailable', from);
		if (content === 'stderr') assert.match(failure.params.message, /solver could not start/);
		assert.equal(f.messages.slice(from).some(message => message.params?.state === 'verified'), false);
	}
	f.settings.executable = path.join(f.dir, 'missing executable');
	const from = f.messages.length;
	f.notify('caravan/verify', { uri: uri(f.file) });
	assert.match((await f.state('unavailable', from)).params.message, /ENOENT/);
});

test('report schema rejects invalid positions and inconsistent success', () => {
	const error = { file: 'test.ml', start_line: 1, start_col: 0, end_line: 1, end_col: 1, kind: 'Type', message: ['bad'] };
	const report = { errors: [error], dependencies: [], annotations: [], members: [], references: [], symbols: [] };
	assert.throws(() => parseReport(JSON.stringify(report), 0), /exit code/);
	assert.throws(() => parseReport('{"errors":[]}', 0), /invalid/);
	error.start_line = 0;
	assert.throws(() => parseReport(JSON.stringify(report), 1), /invalid/);
	report.errors = [];
	assert.equal(parseReport(JSON.stringify(report), 0).errors.length, 0);
	assert.throws(() => parseReport(JSON.stringify(report), 2), /exit code/);
});

test('Raven UTF-8 byte columns become UTF-16 ranges in primary and related source files', { timeout: 15000 }, async t => {
	const f = await fixture(t, 'é😀fail unicode');
	const proof = f.file.replace(/\.ml$/, '.proof');
	await fs.writeFile(proof, 'é😀proof');
	await f.open();
	await f.open(proof);
	f.notify('caravan/verify', { uri: uri(f.file) });
	await f.state('failed');
	const publication = await f.wait(message => message.method === 'textDocument/publishDiagnostics' && message.params.diagnostics.length > 0);
	const diagnostic = publication.params.diagnostics[0];
	assert.deepEqual(diagnostic.range, { start: { line: 0, character: 3 }, end: { line: 0, character: 7 } });
	assert.deepEqual(diagnostic.relatedInformation[0].location.range, { start: { line: 0, character: 1 }, end: { line: 0, character: 3 } });
	assert.equal(utf16Column('é😀x', 5), 1);
});

test('leading related locations attach to the next error and missing library text remains usable', () => {
	const location = { file: 'library.rav', start_line: 3, start_col: 7, end_line: 3, end_col: 9 };
	const report = parseReport(JSON.stringify({
		errors: [{ ...location, kind: 'RelatedLoc', message: ['Inherited', 'contract'] },
			{ ...location, file: 'main.ml', start_line: 1, end_line: 1, start_col: 6, end_col: 7, kind: 'Verification', message: ['Cannot prove'] }],
		dependencies: [], annotations: [], members: [], references: [], symbols: []
	}), 1);
	const normalized = normalizeReport(report, path.join(os.tmpdir(), 'main.ml'), os.tmpdir(), file => file.endsWith('main.ml') ? 'é😀x' : undefined);
	assert.equal(normalized.diagnostics[0].location.start.character, 3);
	assert.equal(normalized.diagnostics[0].related[0].message, 'Inherited\ncontract');
	assert.deepEqual(normalized.diagnostics[0].related[0].location.start, { line: 2, character: 7 });
});

test('successful reports containing warnings retain diagnostics and explicit warning state', { timeout: 15000 }, async t => {
	const f = await fixture(t, 'warning');
	await f.open();
	f.notify('caravan/verify', { uri: uri(f.file) });
	await f.state('verifiedWithWarnings');
	const publication = await f.wait(message => message.method === 'textDocument/publishDiagnostics' && message.params.diagnostics.length > 0);
	assert.equal(publication.params.diagnostics[0].severity, 2);
	assert.equal(publication.params.diagnostics[0].message, 'Trusted specification');
	assert.equal(f.messages.some(message => message.params?.state === 'failed' || message.params?.state === 'verified'), false);
});

test('independent verification owners retain diagnostics and verifyOnSave is respected', { timeout: 15000 }, async t => {
	const f = await fixture(t, 'fail');
	const other = path.join(f.dir, 'other.ml');
	await fs.writeFile(other, 'fail');
	await f.open();
	await f.open(other);
	f.notify('caravan/verify', { uri: uri(f.file) });
	await f.state('failed');
	f.notify('caravan/verify', { uri: uri(other) });
	await f.state('failed', 0, other);
	const from = f.messages.length;
	f.notify('textDocument/didChange', { textDocument: { uri: uri(f.file), version: 2 }, contentChanges: [{ text: 'let x = 2' }] });
	await f.state('outdated', from);
	assert.equal(f.messages.slice(from).some(message => message.method === 'textDocument/publishDiagnostics' && message.params.uri === uri(other) && message.params.diagnostics.length === 0), false);
	f.settings.verifyOnSave = false;
	await fs.writeFile(f.file, 'let x = 2');
	const runs = (await fs.readFile(path.join(f.dir, 'runs'), 'utf8')).trim().split('\n').length;
	f.notify('textDocument/didSave', { textDocument: { uri: uri(f.file) } });
	await delay(100);
	assert.equal((await fs.readFile(path.join(f.dir, 'runs'), 'utf8')).trim().split('\n').length, runs);
	f.notify('caravan/verify', { uri: uri(f.file) });
	await f.state('verified', from);
});

test('process cancellation removes queued work and terminates child process groups', { timeout: 10000 }, async t => {
	const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'caravan cancel '));
	t.after(() => fs.rm(dir, { recursive: true, force: true }));
	const marker = path.join(dir, 'child survived');
	const launcher = path.join(dir, 'launcher.cjs');
	await fs.writeFile(launcher, `const {spawn}=require('node:child_process'); const fs=require('node:fs'); spawn(process.execPath,['-e',${JSON.stringify(`setTimeout(()=>require('node:fs').writeFileSync(${JSON.stringify(marker)},'alive'),700)`)}],{stdio:'ignore'}); fs.writeFileSync(${JSON.stringify(path.join(dir, 'started'))},'yes'); setTimeout(()=>{},5000);`);
	const processes = new VerificationProcesses(1);
	const running = new AbortController();
	const queued = new AbortController();
	const first = processes.run(process.execPath, [launcher], dir, running.signal);
	const second = processes.run(process.execPath, ['-e', "throw Error('queued work started')"], dir, queued.signal);
	const firstRejected = assert.rejects(first, /cancelled/);
	const secondRejected = assert.rejects(second, /cancelled/);
	queued.abort();
	for (let attempt = 0; attempt < 100; attempt++) {
		try { await fs.access(path.join(dir, 'started')); break; } catch { await delay(10); }
	}
	running.abort();
	await Promise.all([firstRejected, secondRejected]);
	await delay(900);
	await assert.rejects(fs.access(marker), { code: 'ENOENT' });
	assert.equal((await processes.run(process.execPath, ['-e', "process.stdout.write('ok')"], dir, new AbortController().signal)).stdout, 'ok');
});


test('automatic toolchain uses matching compiler environment and explicit launcher overrides it', { timeout: 15000 }, async t => {
	const bundleRoot = path.join(os.tmpdir(), 'managed toolchain');
	const f = await fixture(t, 'let x = 1', { executable: process.execPath, bundleRoot });
	f.settings.executable = '';
	await f.open();
	f.notify('caravan/verify', { uri: uri(f.file) });
	await f.state('verified');
	let environment = JSON.parse(await fs.readFile(path.join(f.dir, 'environment'), 'utf8'));
	assert.equal(environment.OCAMLLIB, path.join(bundleRoot, 'lib', 'ocaml'));
	assert.equal(environment.PATH.split(path.delimiter)[0], path.join(bundleRoot, 'bin'));
	const from = f.messages.length;
	f.notify('caravan/toolchain', { executable: path.join(f.dir, 'missing'), bundleRoot });
	await f.state('outdated', from);
	f.settings.executable = process.execPath;
	f.notify('caravan/verify', { uri: uri(f.file) });
	await f.state('verified', from);
	environment = JSON.parse(await fs.readFile(path.join(f.dir, 'environment'), 'utf8'));
	assert.equal(environment.OCAMLLIB, process.env.OCAMLLIB);
	assert.equal(environment.PATH, process.env.PATH);
});

test('toolchain changes cancel in-flight verification and invalidate unchanged document versions', { timeout: 15000 }, async t => {
	const f = await fixture(t, 'slow fail');
	await f.open();
	f.notify('caravan/verify', { uri: uri(f.file) });
	await f.state('verifying');
	for (let attempt = 0; attempt < 100; attempt++) {
		try { await fs.access(path.join(f.dir, 'runs')); break; } catch { await delay(10); }
	}
	const from = f.messages.length;
	f.notify('caravan/toolchain', { executable: process.execPath });
	assert.equal((await f.state('outdated', from)).params.version, 1);
	await delay(1300);
	assert.equal(f.messages.slice(from).some(message => ['failed', 'verified', 'unavailable'].includes(message.params?.state)), false);
	f.notify('caravan/verify', { uri: uri(f.file) });
	await f.state('failed', from);
	const changed = f.messages.length;
	f.notify('caravan/toolchain', { executable: process.execPath });
	await f.state('outdated', changed);
	await f.wait(message => message.method === 'textDocument/publishDiagnostics' && message.params.diagnostics.length === 0, changed);
	const invalid = f.messages.length;
	for (const value of [null, {}, { executable: 42 }, { executable: '' }, { executable: process.execPath, bundleRoot: 42 }]) f.notify('caravan/toolchain', value);
	await delay(100);
	assert.equal(f.messages.slice(invalid).some(message => message.params?.state === 'outdated'), false);
	f.notify('caravan/verify', { uri: uri(f.file) });
	await f.state('failed', invalid);
});
