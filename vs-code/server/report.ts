import * as path from 'node:path';

export interface Position { line: number; character: number }
export interface SourceLocation { file: string; start: Position; end: Position }
export interface ReportDiagnostic {
	severity: 'error' | 'warning'; kind: string;
	location: SourceLocation; message: string;
	related: { location: SourceLocation; message: string }[];
}
export interface FileResult {
	file: string; verified: boolean; diagnostics: ReportDiagnostic[]; dependencies: string[];
}
interface RavenError {
	file: string; start_line: number; start_col: number; end_line: number; end_col: number;
	kind: string; message: string[];
}
export interface RavenReport {
	errors: RavenError[]; dependencies: string[];
	annotations: unknown[]; members: unknown[]; references: unknown[]; symbols: unknown[];
}
const auxiliaryKinds = new Set(['RelatedLoc', 'Warning', 'Limit', 'Counterexample', 'Branch']);
function object(value: unknown): value is Record<string, unknown> {
	return typeof value === 'object' && value !== null && !Array.isArray(value);
}
function ravenError(value: unknown): value is RavenError {
	if (!object(value) || typeof value.file !== 'string' || !value.file || typeof value.kind !== 'string' || !value.kind
		|| !Array.isArray(value.message) || !value.message.every(item => typeof item === 'string')
		|| !Number.isInteger(value.start_line) || (value.start_line as number) < 1
		|| !Number.isInteger(value.end_line) || (value.end_line as number) < 1
		|| !Number.isInteger(value.start_col) || (value.start_col as number) < 0
		|| !Number.isInteger(value.end_col) || (value.end_col as number) < 0) return false;
	return (value.start_line as number) < (value.end_line as number)
		|| (value.start_line === value.end_line && (value.start_col as number) <= (value.end_col as number));
}
export function parseReport(text: string, exitCode: number | null): RavenReport {
	let value: unknown;
	try { value = JSON.parse(text); } catch { throw new Error('Caravan returned invalid JSON'); }
	if (!object(value) || !Array.isArray(value.errors) || !value.errors.every(ravenError)
		|| !Array.isArray(value.dependencies) || !value.dependencies.every(item => typeof item === 'string' && item.length > 0)
		|| !Array.isArray(value.annotations) || !Array.isArray(value.members)
		|| !Array.isArray(value.references) || !Array.isArray(value.symbols)) throw new Error('Caravan returned an invalid Raven LSP report');
	const failed = value.errors.some(error => !auxiliaryKinds.has(error.kind));
	if (exitCode !== (failed ? 1 : 0)) throw new Error(`Caravan report disagrees with exit code ${exitCode}`);
	return { errors: value.errors, dependencies: value.dependencies, annotations: value.annotations,
		members: value.members, references: value.references, symbols: value.symbols };
}

/** Round partial UTF-8 code points down when converting compiler byte columns. */
export function utf16Column(line: string, byteColumn: number): number {
	let bytes = 0;
	let characters = 0;
	for (const character of line) {
		const size = Buffer.byteLength(character, 'utf8');
		if (bytes + size > byteColumn) break;
		bytes += size;
		characters += character.length;
	}
	return characters;
}

export function normalizeReport(report: RavenReport, root: string, cwd: string, readText: (file: string) => string | undefined): FileResult {
	const files = new Map<string, string[] | undefined>();
	const location = (error: RavenError): SourceLocation => {
		const file = path.resolve(cwd, error.file);
		if (!files.has(file)) files.set(file, readText(file)?.split('\n'));
		const lines = files.get(file);
		const position = (line: number, column: number): Position => {
			// Embedded library sources may not be available in the workspace.
			if (!lines) return { line: line - 1, character: column };
			const index = Math.min(line - 1, lines.length - 1);
			return { line: index, character: utf16Column(lines[index], column) };
		};
		return { file, start: position(error.start_line, error.start_col), end: position(error.end_line, error.end_col) };
	};
	const diagnostics: ReportDiagnostic[] = [];
	let previous: ReportDiagnostic | undefined;
	let pending: ReportDiagnostic['related'] = [];
	for (const error of report.errors) {
		if (error.kind === 'RelatedLoc') {
			const related = { location: location(error), message: error.message.join('\n') };
			if (previous) previous.related.push(related); else pending.push(related);
		} else if (!['Limit', 'Counterexample', 'Branch'].includes(error.kind)) {
			previous = { severity: error.kind === 'Warning' ? 'warning' : 'error', kind: error.kind,
				location: location(error), message: error.message.join('\n'), related: pending };
			pending = [];
			diagnostics.push(previous);
		}
	}
	return { file: root, verified: !report.errors.some(error => !auxiliaryKinds.has(error.kind)), diagnostics, dependencies: report.dependencies };
}
