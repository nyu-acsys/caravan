import * as path from 'node:path';
import { URI } from 'vscode-uri';
import type { Hover, MarkupContent } from 'vscode-languageserver/node';
import type { NormalizedContract, Position, SourceLocation } from './report';

function externalContract(contract: NormalizedContract, root: string): boolean {
	return contract.location.file === root && /\.(mli|proof)$/.test(contract.sourceLocation.file);
}

export function sourceExcerpt(location: SourceLocation, readText: (file: string) => string | undefined): string | undefined {
	const text = readText(location.file);
	if (text === undefined) return undefined;
	const lines = text.split('\n');
	const offset = (position: Position) => lines.slice(0, position.line).reduce((sum, line) => sum + line.length + 1, 0) + position.character;
	return text.slice(offset(location.start), offset(location.end)).trim();
}

export function contractBody(contract: NormalizedContract, readText: (file: string) => string | undefined): string {
	const original = sourceExcerpt(contract.sourceLocation, readText)
		|| contract.clauses.map(clause => `${clause.keyword} ${clause.text}`.trimEnd()).join('\n');
	return original.startsWith('(*@') && original.endsWith('*)') ? original.slice(3, -2).trim() : original;
}

export function annotationMarkdown(title: string, text: string, origin: SourceLocation, workspace: string): MarkupContent {
	const ticks = (text.match(/`+/g) ?? []).reduce((longest, run) => Math.max(longest, run.length), 2);
	const fence = '`'.repeat(ticks + 1);
	const file = (path.relative(workspace, origin.file) || path.basename(origin.file)).split(path.sep).join('/');
	const label = `${file}:${origin.start.line + 1}`
		.replace(/[\\`*_[\]<>]/g, '\\$&');
	const target = URI.file(origin.file).with({ fragment: `L${origin.start.line + 1},${origin.start.character + 1}` }).toString();
	return { kind: 'markdown', value: `${title} from [${label}](<${target}>)\n\n${fence}caravan-proof\n${text}\n${fence}` };
}

export function contractHover(contracts: NormalizedContract[], root: string, position: Position,
	readText: (file: string) => string | undefined, workspace: string): Hover | null {
	const before = (left: Position, right: Position) => left.line < right.line || (left.line === right.line && left.character < right.character);
	const contract = contracts.find(contract => externalContract(contract, root)
		&& !before(position, contract.location.start) && before(position, contract.location.end));
	if (!contract) return null;
	return { range: { start: contract.location.start, end: contract.location.end },
		contents: annotationMarkdown('Contract', contractBody(contract, readText), contract.sourceLocation, workspace) };
}
