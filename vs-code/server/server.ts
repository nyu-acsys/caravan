import { createConnection, TextDocuments, TextDocumentSyncKind, DiagnosticSeverity,
	type Diagnostic, type InitializeParams, type WorkspaceFolder } from 'vscode-languageserver/node';
import { TextDocument } from 'vscode-languageserver-textdocument';
import { URI } from 'vscode-uri';
import * as fs from 'node:fs';
import * as path from 'node:path';
import { toolchainEnvironment } from '../shared/toolchain';
import { VerificationProcesses } from './verificationProcesses';
import { parseReport, normalizeReport, normalizeContracts, type RavenReport, type NormalizedContract } from './report';
import { contractLenses, contractHover } from './contracts';
import { verificationStateNotification, verifyNotification, type VerificationState, type VerifyParams, toolchainNotification, type ToolchainSelection } from '../shared/protocol';

interface Settings {
	executable: string; arguments: string[]; includePaths: string[];
	smtTimeout: number; verifyOnSave: boolean; showContractLenses: boolean; cwd: string;
}
interface Owner {
	generation: number; dependencies?: Set<string>; abort?: AbortController;
	diagnostics: Map<string, Diagnostic[]>;
	state: VerificationState; message?: string;
	annotationGeneration: number; annotationAbort?: AbortController;
	annotations?: Promise<NormalizedContract[]>; annotationStamps?: Map<string, string>; annotationDependencies?: Set<string>;
}
const defaults: Settings = { executable: '', arguments: [], includePaths: [], smtTimeout: 10000, verifyOnSave: true, showContractLenses: true, cwd: '' };
const connection = createConnection();
const documents = new TextDocuments(TextDocument);
const processes = new VerificationProcesses(2);
const annotationProcesses = new VerificationProcesses(1);
const owners = new Map<string, Owner>();
const revisions = new Map<string, number>();
const dirty = new Set<string>();
const initialChanges = new Set<string>();
const diskStamps = new Map<string, string>();
let codeLensRefresh = false;
let configuration = false;
let workspaceFolders = false;
let globalSettings: unknown = {};
let folders: WorkspaceFolder[] = [];
let shuttingDown = false;
let toolchain: ToolchainSelection | undefined;

function fileOf(uri: string): string | undefined {
	const parsed = URI.parse(uri);
	return parsed.scheme === 'file' ? path.resolve(parsed.fsPath) : undefined;
}
function rootOf(file: string): string { return file.replace(/\.(mli|proof)$/, '.ml'); }
function relevant(file: string): boolean { return /\.(ml|mli|proof)$/.test(file); }
function siblings(file: string): string[] {
	const stem = file.replace(/\.ml$/, '');
	return [file, `${stem}.mli`, `${stem}.proof`];
}
function ownerOf(root: string): Owner {
	let owner = owners.get(root);
	if (!owner) { owner = { generation: 0, annotationGeneration: 0, diagnostics: new Map(), state: 'unchecked' }; owners.set(root, owner); }
	return owner;
}
function state(root: string, value: VerificationState, message?: string): void {
	const owner = owners.get(root);
	if (owner) { owner.state = value; owner.message = message; }
	const uris = new Set([URI.file(root).toString()]);
	for (const document of documents.all()) {
		const file = fileOf(document.uri);
		if (file && rootOf(file) === root) uris.add(document.uri);
	}
	for (const uri of uris) connection.sendNotification(verificationStateNotification, {
		uri, version: documents.get(uri)?.version ?? 0, state: value, ...(message ? { message } : {})
	});
}
function publish(uris: Iterable<string>): void {
	for (const uri of new Set(uris)) {
		const diagnostics = [...owners.values()].flatMap(owner => owner.diagnostics.get(uri) ?? []);
		connection.sendDiagnostics({ uri, diagnostics });
	}
}
function clear(owner: Owner): void {
	const uris = [...owner.diagnostics.keys()];
	owner.diagnostics.clear();
	publish(uris);
}
function knownDependencies(root: string, owner: Owner): Set<string> | undefined {
	if (!owner.dependencies && !owner.annotationDependencies) return undefined;
	return new Set([...siblings(root), ...(owner.dependencies ?? []), ...(owner.annotationDependencies ?? [])]);
}
function clearAnnotations(owner: Owner): void {
	owner.annotationGeneration++;
	owner.annotationAbort?.abort();
	owner.annotationAbort = undefined;
	owner.annotations = undefined;
	owner.annotationStamps = undefined;
}
function refreshAnnotations(): void {
	if (codeLensRefresh && !shuttingDown) void connection.sendRequest('workspace/codeLens/refresh').catch(() => undefined);
}
function invalidate(file: string): void {
	if (!relevant(file)) return;
	revisions.set(file, (revisions.get(file) ?? 0) + 1);
	for (const [root, owner] of owners) {
		const dependencies = knownDependencies(root, owner);
		if (!dependencies || dependencies.has(file)) {
			clearAnnotations(owner);
			owner.generation++;
			owner.abort?.abort();
			owner.abort = undefined;
			clear(owner);
			state(root, 'outdated');
		}
	}
	refreshAnnotations();
}
function selectToolchain(value: unknown): void {
	if (typeof value !== 'object' || value === null) return;
	const candidate = value as Record<string, unknown>;
	if (typeof candidate.executable !== 'string' || !candidate.executable.trim() || candidate.executable.includes('\0')
		|| (candidate.bundleRoot !== undefined && (typeof candidate.bundleRoot !== 'string'
			|| !path.isAbsolute(candidate.bundleRoot) || candidate.bundleRoot.includes('\0')))) return;
	toolchain = { executable: candidate.executable, ...(typeof candidate.bundleRoot === 'string' ? { bundleRoot: candidate.bundleRoot } : {}) };
	for (const [root, owner] of owners) {
		clearAnnotations(owner);
		owner.generation++;
		owner.abort?.abort();
		owner.abort = undefined;
		clear(owner);
		state(root, 'outdated');
	}
	refreshAnnotations();
}
function workspaceFor(file: string): string {
	return folders.map(folder => fileOf(folder.uri)).filter((folder): folder is string => !!folder)
		.filter(folder => file === folder || file.startsWith(folder + path.sep))
		.sort((a, b) => b.length - a.length)[0] ?? path.dirname(file);
}
function settingsFrom(value: unknown): Settings {
	const v = typeof value === 'object' && value !== null ? value as Record<string, unknown> : {};
	const strings = (x: unknown): x is string[] => Array.isArray(x) && x.every(item => typeof item === 'string');
	return {
		executable: typeof v.executable === 'string' && v.executable.trim() ? v.executable : defaults.executable,
		arguments: strings(v.arguments) ? v.arguments : [], includePaths: strings(v.includePaths) ? v.includePaths : [],
		smtTimeout: typeof v.smtTimeout === 'number' && Number.isInteger(v.smtTimeout) && v.smtTimeout > 0 ? v.smtTimeout : defaults.smtTimeout,
		verifyOnSave: typeof v.verifyOnSave === 'boolean' ? v.verifyOnSave : defaults.verifyOnSave,
		showContractLenses: typeof v.showContractLenses === 'boolean' ? v.showContractLenses : defaults.showContractLenses,
		cwd: typeof v.cwd === 'string' ? v.cwd : ''
	};
}
async function settings(uri: string): Promise<Settings> {
	return settingsFrom(configuration ? await connection.workspace.getConfiguration({ scopeUri: uri, section: 'caravan' }) : globalSettings);
}
function hasDirty(dependencies?: Set<string>): boolean {
	for (const document of documents.all()) {
		const file = fileOf(document.uri);
		if (!file || !relevant(file) || (dependencies && !dependencies.has(file))) continue;
		let saved: string | undefined;
		try { saved = fs.readFileSync(file, 'utf8'); } catch { saved = undefined; }
		if (saved === document.getText()) dirty.delete(file); else dirty.add(file);
	}
	return [...dirty].some(file => !dependencies || dependencies.has(file));
}
function diskStamp(file: string): string {
	try { const stat = fs.statSync(file); return `${stat.mtimeMs}:${stat.size}`; } catch { return 'missing'; }
}
function launch(root: string, config: Settings, annotationsOnly = false): { executable: string; args: string[]; cwd: string; env?: NodeJS.ProcessEnv } {
	const workspace = workspaceFor(root);
	const cwd = config.cwd ? path.resolve(workspace, config.cwd) : workspace;
	const selected = config.executable || toolchain?.executable || 'caravan';
	const executable = selected.includes('/') || selected.includes('\\') ? path.resolve(cwd, selected) : selected;
	const bundleRoot = !config.executable ? toolchain?.bundleRoot : undefined;
	const env = bundleRoot ? toolchainEnvironment(bundleRoot) : undefined;
	const args = [...config.arguments, '--lsp-mode', '--lsp-annotations',
		...(annotationsOnly ? ['--lsp-annotations-only'] : ['--smt-timeout', String(config.smtTimeout)]),
		...config.includePaths.flatMap(directory => ['-I', path.resolve(cwd, directory)]), root];
	return { executable, args, cwd, env };
}
function sourceText(source: string): string | undefined {
	const document = documents.get(URI.file(source).toString());
	if (document) return document.getText();
	try { return fs.readFileSync(source, 'utf8'); } catch { return undefined; }
}
function reportDependencies(report: RavenReport, root: string, cwd: string): Set<string> {
	const dependencies = new Set(siblings(root));
	for (const dependency of report.dependencies) dependencies.add(path.resolve(cwd, dependency));
	for (const error of report.errors) dependencies.add(path.resolve(cwd, error.file));
	for (const annotation of report.annotations) {
		dependencies.add(path.resolve(cwd, annotation.file));
		dependencies.add(path.resolve(cwd, annotation.source_loc.file));
		for (const clause of annotation.clauses) dependencies.add(path.resolve(cwd, clause.file));
	}
	return dependencies;
}
function checkedReport(stdout: string, code: number | null, root: string, cwd: string): RavenReport {
	const parsed = parseReport(stdout, code);
	if (!parsed.dependencies.some(dependency => path.resolve(cwd, dependency) === root)) {
		throw new Error('Caravan report omitted the requested implementation dependency');
	}
	return parsed;
}
async function annotations(root: string, uri: string, owner: Owner): Promise<NormalizedContract[]> {
	const generation = owner.annotationGeneration;
	try {
		const config = await settings(uri);
		if (shuttingDown || generation !== owner.annotationGeneration) return [];
		const known = knownDependencies(root, owner);
		if (hasDirty(known) || !fs.existsSync(root)) return [];
		const snapshot = new Map(revisions);
		const { executable, args, cwd, env } = launch(root, config, true);
		const abort = new AbortController();
		owner.annotationAbort = abort;
		const output = await annotationProcesses.run(executable, args, cwd, abort.signal, env);
		if (shuttingDown || abort.signal.aborted || generation !== owner.annotationGeneration) return [];
		const report = checkedReport(output.stdout, output.code, root, cwd);
		const dependencies = reportDependencies(report, root, cwd);
		owner.annotationDependencies = dependencies;
		if (hasDirty(dependencies) || [...dependencies].some(file => (revisions.get(file) ?? 0) !== (snapshot.get(file) ?? 0))) return [];
		owner.annotationStamps = new Map([...dependencies].map(file => [file, diskStamp(file)]));
		return normalizeContracts(report, cwd, sourceText);
	} catch {
		// Older toolchains may not support frontend-only annotation reports.
		return [];
	} finally {
		if (generation === owner.annotationGeneration) owner.annotationAbort = undefined;
	}
}
async function contractsFor(uri: string): Promise<NormalizedContract[]> {
	const root = fileOf(uri);
	if (!root || !root.endsWith('.ml') || shuttingDown) return [];
	const owner = ownerOf(root);
	if (owner.annotationStamps) {
		for (const [file, stamp] of owner.annotationStamps) {
			if (diskStamp(file) !== stamp) { invalidate(file); break; }
		}
	}
	if (hasDirty(knownDependencies(root, owner))) return [];
	const generation = owner.annotationGeneration;
	owner.annotations ??= annotations(root, uri, owner);
	const result = await owner.annotations;
	return generation !== owner.annotationGeneration || hasDirty(knownDependencies(root, owner)) ? [] : result;
}
async function verify(uri: string, onSave = false): Promise<void> {
	const file = fileOf(uri);
	if (!file || !relevant(file) || shuttingDown) return;
	const root = rootOf(file);
	const owner = ownerOf(root);
	owner.abort?.abort();
	const generation = ++owner.generation;
	owner.abort = undefined;
	try {
		const config = await settings(uri);
		if (shuttingDown || generation !== owner.generation) return;
		if (onSave && !config.verifyOnSave) return;
		clear(owner);
		if (!fs.existsSync(root)) { state(root, 'unavailable', `No implementation found: ${root}`); return; }
		const known = knownDependencies(root, owner);
		if (hasDirty(known)) { state(root, 'outdated', 'Save changed OCaml and proof files before verifying.'); return; }
		const snapshot = new Map(revisions);
		const { executable, args, cwd, env } = launch(root, config);
		const abort = new AbortController();
		owner.abort = abort;
		state(root, 'verifying');
		const output = await processes.run(executable, args, cwd, abort.signal, env);
		if (shuttingDown || abort.signal.aborted || generation !== owner.generation) return;
		let parsed;
		try { parsed = checkedReport(output.stdout, output.code, root, cwd); }
		catch (error) { throw new Error(`${error instanceof Error ? error.message : String(error)}${output.stderr.trim() ? `: ${output.stderr.trim().slice(0, 2000)}` : ''}`); }
		const report = { results: [normalizeReport(parsed, root, cwd, sourceText)] };
		const dependencies = reportDependencies(parsed, root, cwd);
		owner.dependencies = dependencies;
		if (hasDirty(dependencies) || [...dependencies].some(dependency => (revisions.get(dependency) ?? 0) !== (snapshot.get(dependency) ?? 0))) {
			state(root, 'outdated', 'A dependency changed during verification.'); return;
		}
		const diagnostics = new Map<string, Diagnostic[]>();
		for (const result of report.results) {
			const resultUri = URI.file(path.resolve(cwd, result.file)).toString();
			if (!diagnostics.has(resultUri)) diagnostics.set(resultUri, []);
			for (const item of result.diagnostics) {
				const targetUri = URI.file(path.resolve(cwd, item.location.file)).toString();
				const items = diagnostics.get(targetUri) ?? [];
				items.push({ range: { start: item.location.start, end: item.location.end },
					severity: item.severity === 'error' ? DiagnosticSeverity.Error : DiagnosticSeverity.Warning,
					source: 'Caravan', code: item.kind, message: item.message,
					relatedInformation: item.related.map(related => ({
						location: { uri: URI.file(path.resolve(cwd, related.location.file)).toString(), range: { start: related.location.start, end: related.location.end } },
						message: related.message
					})) });
				diagnostics.set(targetUri, items);
			}
		}
		owner.diagnostics = diagnostics;
		publish(diagnostics.keys());
		const verified = report.results.every(result => result.verified);
		const warnings = report.results.some(result => result.diagnostics.some(diagnostic => diagnostic.severity === 'warning'));
		state(root, verified ? warnings ? 'verifiedWithWarnings' : 'verified' : 'failed');
	} catch (error) {
		if (!shuttingDown && generation === owner.generation) {
			const message = error instanceof Error ? error.message : String(error);
			connection.console.error(message);
			state(root, 'unavailable', message);
		}
	} finally {
		if (generation === owner.generation) owner.abort = undefined;
	}
}

connection.onInitialize((params: InitializeParams) => {
	selectToolchain(params.initializationOptions?.toolchain);
	codeLensRefresh = params.capabilities.workspace?.codeLens?.refreshSupport === true;
	configuration = params.capabilities.workspace?.configuration === true;
	workspaceFolders = params.capabilities.workspace?.workspaceFolders === true;
	folders = params.workspaceFolders ?? (params.rootUri ? [{ uri: params.rootUri, name: 'workspace' }] : []);
	return { capabilities: { hoverProvider: true, codeLensProvider: { resolveProvider: false }, textDocumentSync: { openClose: true, change: TextDocumentSyncKind.Incremental, save: { includeText: false } },
		workspace: { workspaceFolders: { supported: true, changeNotifications: true } } } };
});
connection.onInitialized(() => {
	if (!workspaceFolders) return;
	connection.workspace.onDidChangeWorkspaceFolders(event => {
		folders = folders.filter(folder => !event.removed.some(removed => removed.uri === folder.uri)).concat(event.added);
		for (const [root, owner] of owners) { clearAnnotations(owner); owner.generation++; owner.abort?.abort(); clear(owner); state(root, 'outdated'); }
		refreshAnnotations();
	});
});
connection.onDidChangeConfiguration(event => {
	globalSettings = event.settings?.caravan ?? {};
	for (const [root, owner] of owners) { clearAnnotations(owner); owner.generation++; owner.abort?.abort(); clear(owner); state(root, 'outdated'); }
	refreshAnnotations();
});
connection.onDidChangeWatchedFiles(event => {
	for (const change of event.changes) {
		const file = fileOf(change.uri);
		if (!file) continue;
		const stamp = diskStamp(file);
		if (diskStamps.get(file) === stamp) continue;
		diskStamps.set(file, stamp);
		invalidate(file);
	}
});
connection.onCodeLens(async (params, token) => {
	const root = fileOf(params.textDocument.uri);
	if (!root || !root.endsWith('.ml') || shuttingDown || token.isCancellationRequested) return [];
	if (!(await settings(params.textDocument.uri)).showContractLenses) return [];
	const result = await contractsFor(params.textDocument.uri);
	return token.isCancellationRequested ? [] : contractLenses(result, root);
});
connection.onHover(async (params, token) => {
	const root = fileOf(params.textDocument.uri);
	if (!root || !root.endsWith('.ml') || shuttingDown || token.isCancellationRequested) return null;
	const result = await contractsFor(params.textDocument.uri);
	return token.isCancellationRequested ? null : contractHover(result, root, params.position, sourceText, workspaceFor(root));
});
connection.onNotification(toolchainNotification, selectToolchain);
connection.onNotification(verifyNotification, (params: VerifyParams) => {
	if (params && typeof params.uri === 'string') void verify(params.uri);
});
documents.onDidOpen(event => {
	const file = fileOf(event.document.uri);
	if (file && relevant(file)) {
		initialChanges.add(event.document.uri);
		diskStamps.set(file, diskStamp(file));
		const owner = ownerOf(rootOf(file));
		state(rootOf(file), owner.state, owner.message);
	}
});
documents.onDidChangeContent(event => {
	const file = fileOf(event.document.uri);
	if (!file || !relevant(file)) return;
	let saved: string | undefined;
	try { saved = fs.readFileSync(file, 'utf8'); } catch { saved = undefined; }
	if (saved === event.document.getText()) dirty.delete(file); else dirty.add(file);
	if (initialChanges.delete(event.document.uri) && !dirty.has(file)) return;
	invalidate(file);
});
documents.onDidSave(event => {
	const file = fileOf(event.document.uri);
	if (!file || !relevant(file)) return;
	dirty.delete(file);
	diskStamps.set(file, diskStamp(file));
	invalidate(file);
	void verify(event.document.uri, true);
});
documents.onDidClose(event => {
	initialChanges.delete(event.document.uri);
	const file = fileOf(event.document.uri);
	if (!file) return;
	if (dirty.delete(file)) invalidate(file);
	const root = rootOf(file);
	if (!documents.all().some(document => { const open = fileOf(document.uri); return open && rootOf(open) === root; })) {
		const owner = owners.get(root);
		if (owner) { clearAnnotations(owner); owner.generation++; owner.abort?.abort(); clear(owner); owners.delete(root); }
	}
});
function stop(): void {
	shuttingDown = true;
	for (const owner of owners.values()) { clearAnnotations(owner); owner.generation++; owner.abort?.abort(); }
}
connection.onShutdown(stop);
connection.onExit(stop);
process.on('SIGTERM', () => { stop(); process.exit(0); });
process.on('SIGINT', () => { stop(); process.exit(0); });
process.on('exit', stop);
documents.listen(connection);
connection.listen();
