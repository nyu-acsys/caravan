const test = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const os = require('node:os');
const path = require('node:path');
const { VerificationProcesses, UnsupportedServerError } = require('../out/server/verificationProcesses');

const delay = ms => new Promise(resolve => setTimeout(resolve, ms));
const prelude = `
const fs = require('node:fs');
let input = '';
process.stdin.setEncoding('utf8');
process.stdin.on('data', data => input += data);
const send = message => process.stdout.write(JSON.stringify(message) + '\\n');
const partial = (text, phase = 'typed') => send({id:1,partial:text,phase});
const final = (exit = 0, stdout = 'done', stderr = '') => send({id:1,exit,stdout,stderr});
process.stdin.on('end', () => {
 const request = JSON.parse(input);
 if (process.argv.at(-1) !== '--server' || request.id !== 1 || request.partial !== true || request.cwd !== process.cwd()) throw Error('bad server request');
`;

async function fixture(t, body, processes = new VerificationProcesses()) {
	const dir = await fs.mkdtemp(path.join(os.tmpdir(), 'caravan stream '));
	const script = path.join(dir, 'mock verifier.cjs');
	const controller = new AbortController();
	await fs.writeFile(script, prelude + body + '\n});\n');
	t.after(() => controller.abort());
	t.after(() => fs.rm(dir, { recursive: true, force: true }));
	return { dir, script, processes, serve: (callback = () => {}, signal = controller.signal, args = [], env) =>
		processes.serve(process.execPath, [script], args, dir, signal, env, callback) };
}

async function waitFor(file) {
	for (let i = 0; i < 500; i++) {
		try { await fs.access(file); return; } catch (error) { if (error.code !== 'ENOENT') throw error; }
		await delay(10);
	}
	throw new Error(`Timed out waiting for ${file}`);
}

test('server delivers UTF-8 partial snapshots before completion and sends request arguments and environment', { timeout: 10000 }, async t => {
	const f = await fixture(t, `
 fs.writeFileSync('request', JSON.stringify({args:request.args,environment:process.env.CARAVAN_STREAM_TEST}));
 const bytes = Buffer.from(JSON.stringify({id:1,partial:'é😀 snapshot',phase:'typed'}) + '\\n');
 const split = bytes.indexOf(Buffer.from('😀')) + 2;
 process.stdout.write(bytes.subarray(0,split));
 setTimeout(() => process.stdout.write(bytes.subarray(split)), 10);
 const timer = setInterval(() => { if (fs.existsSync('release')) {
  clearInterval(timer); partial('scheduled','scheduled'); partial('progress','progress');
  process.stderr.write('worker warning'); final(1,'final report','report warning; ');
 } }, 10);
 `);
	const updates = [];
	let received;
	const first = new Promise(resolve => { received = resolve; });
	let settled = false;
	const result = f.serve((stdout, phase) => { updates.push([stdout, phase]); received(); }, undefined,
		['--lsp-mode', 'main with spaces.ml'], { ...process.env, CARAVAN_STREAM_TEST: 'present' });
	result.then(() => { settled = true; }, () => { settled = true; });
	await first;
	assert.deepEqual(updates, [['é😀 snapshot', 'typed']]);
	assert.equal(settled, false);
	assert.deepEqual(JSON.parse(await fs.readFile(path.join(f.dir, 'request'), 'utf8')),
		{ args: ['--lsp-mode', 'main with spaces.ml'], environment: 'present' });
	await fs.writeFile(path.join(f.dir, 'release'), 'yes');
	assert.deepEqual(await result, { stdout: 'final report', stderr: 'report warning; worker warning', code: 1 });
	assert.deepEqual(updates.map(update => update[1]), ['typed', 'scheduled', 'progress']);
});

test('server limits each snapshot while allowing cumulative output above 4 MiB', { timeout: 10000 }, async t => {
	const f = await fixture(t, `for (let i=0;i<5;i++) partial('x'.repeat(1024*1024),'progress'); final();`);
	let count = 0;
	const result = await f.serve((text, phase) => {
		assert.equal(text.length, 1024 * 1024);
		assert.equal(phase, 'progress');
		count++;
	});
	assert.equal(count, 5);
	assert.equal(result.stdout, 'done');
});

test('server rejects malformed, mismatched, duplicate and missing frames', { timeout: 15000 }, async t => {
	const cases = [
		[`process.stdout.write('not json\\n');`, /JSON|Unexpected/],
		[`send({id:2,partial:'wrong',phase:'typed'});`, /ID mismatch/],
		[`send({id:1,partial:'bad phase',phase:'other'});`, /Invalid.*frame/],
		[`send({id:1,exit:'0',stdout:'bad exit',stderr:''});`, /Invalid.*frame/],
		[`send({id:1,exit:0,stdout:'mixed',stderr:'',partial:'invalid',phase:'typed'});`, /Invalid.*frame/],
		[`final(); final();`, /after final/],
		[`final(); partial('too late');`, /after final/],
		[`process.stdout.write(JSON.stringify({id:1,exit:0,stdout:'incomplete',stderr:''}));`, /Unterminated/],
		[`partial('only partial');`, /without a final/],
		[`process.stdout.write(Buffer.from([0xff,10]));`, /encoded|encoding|UTF-8/i],
	];
	for (const [body, pattern] of cases) {
		const f = await fixture(t, body);
		await assert.rejects(f.serve(), pattern);
	}
});

test('server output limits reject complete frames, unfinished lines and stderr', { timeout: 15000 }, async t => {
	for (const body of [
		`partial('x'.repeat(4*1024*1024));`,
		`process.stdout.write('x'.repeat(4*1024*1024+1));`,
		`process.stderr.write('x'.repeat(4*1024*1024+1)); final();`,
		`process.stderr.write('x'.repeat(3*1024*1024)); final(0,'done','x'.repeat(2*1024*1024));`
	]) {
		const f = await fixture(t, body);
		await assert.rejects(f.serve(), /exceeded 4 MiB/);
	}
});

test('server callback errors stop the child and release the worker', { timeout: 10000 }, async t => {
	const processes = new VerificationProcesses(1);
	const f = await fixture(t, `partial('first'); setTimeout(()=>fs.writeFileSync('survived','yes'),500);`, processes);
	const failure = new Error('callback failed');
	await assert.rejects(f.serve(() => { throw failure; }), error => error === failure);
	await delay(700);
	await assert.rejects(fs.access(path.join(f.dir, 'survived')), { code: 'ENOENT' });
	assert.equal((await processes.run(process.execPath, ['-e', "process.stdout.write('ok')"], f.dir, new AbortController().signal)).stdout, 'ok');
});

test('server and batch runs share the bounded pool and cancellation stops process groups', { timeout: 10000 }, async t => {
	const processes = new VerificationProcesses(1);
	const f = await fixture(t, `
 require('node:child_process').spawn(process.execPath,['-e',"setTimeout(()=>require('node:fs').writeFileSync('survived','yes'),700)"],{stdio:'ignore'});
 fs.writeFileSync('started','yes'); setTimeout(()=>{},5000);
 `, processes);
	const active = new AbortController();
	const queued = new AbortController();
	const running = f.serve(undefined, active.signal);
	const activeRejected = assert.rejects(running, /cancelled/);
	await waitFor(path.join(f.dir, 'started'));
	const waiting = f.serve(undefined, queued.signal);
	const queuedRejected = assert.rejects(waiting, /cancelled/);
	const batch = processes.run(process.execPath, ['-e', "require('node:fs').writeFileSync('batch','yes')"], f.dir, new AbortController().signal);
	queued.abort();
	await queuedRejected;
	await delay(50);
	await assert.rejects(fs.access(path.join(f.dir, 'batch')), { code: 'ENOENT' });
	active.abort();
	await activeRejected;
	await batch;
	await delay(850);
	await assert.rejects(fs.access(path.join(f.dir, 'survived')), { code: 'ENOENT' });
	const cancelled = new AbortController();
	cancelled.abort();
	await assert.rejects(f.serve(undefined, cancelled.signal), /cancelled/);
});

test('only explicit unsupported --server errors qualify for batch fallback', { timeout: 10000 }, async t => {
	for (const message of ["unknown option '--server'.", 'unrecognized option: --server']) {
		const f = await fixture(t, `process.stderr.write(${JSON.stringify(message)}); process.exitCode=2;`);
		await assert.rejects(f.serve(), UnsupportedServerError);
	}
	for (const body of [
		`process.stderr.write('solver crashed'); process.exitCode=2;`,
		`partial('started'); process.stderr.write('unknown option --server'); process.exitCode=2;`,
		`process.stdout.write('malformed\\n'); process.stderr.write('unknown option --server'); process.exitCode=2;`,
		`final(); process.exitCode=2;`,
		`process.stderr.write('unknown option --server');`
	]) {
		const f = await fixture(t, body);
		await assert.rejects(f.serve(), error => error instanceof Error && !(error instanceof UnsupportedServerError));
	}
});

test('unsupported server detection preserves colored stderr when a child exits without reading stdin', { timeout: 10000 }, async t => {
	for (const diagnostic of [
		"caravan: unknown option '\u001b[01m--server\u001b[m'.\nUsage: caravan [OPTION]…\n",
		'caravan: unrecognized option: \u001b[1;31m--server\u001b[0m.\n'
	]) {
		const f = await fixture(t, '');
		// Fill the pipe so an immediate exit also exercises the stdin error handler.
		await fs.writeFile(f.script, `require('node:fs').writeSync(2, ${JSON.stringify(diagnostic)}); process.exit(2);`);
		await assert.rejects(f.serve(undefined, undefined, ['x'.repeat(1024 * 1024)]), error => {
			assert.ok(error instanceof UnsupportedServerError);
			assert.equal(error.message, diagnostic.trim());
			return true;
		});
	}
});
