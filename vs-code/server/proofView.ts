import * as path from 'node:path';
import { URI } from 'vscode-uri';
import type { ProofViewResult } from '../shared/protocol';
import type { NormalizedContract, NormalizedProofStep, Position, SourceLocation } from './report';
import { contractBody } from './contracts';

export interface ProofMetadata {
	contracts: NormalizedContract[];
	steps: NormalizedProofStep[];
}
interface Insertion {
	offset: number;
	indent: string;
	kind: string;
	body: string;
	origin: SourceLocation;
}

/** A reading view; attachment locations come exclusively from the front end. */
export function renderProofView(root: string, source: string, metadata: ProofMetadata,
	readText: (file: string) => string | undefined, workspace: string): ProofViewResult {
	const lines = source.split('\n');
	const starts: number[] = [0];
	for (let i = 0; i < source.length; i++) if (source[i] === '\n') starts.push(i + 1);
	const offset = (position: Position): number => {
		const start = starts[position.line];
		if (start === undefined || position.character > lines[position.line].replace(/\r$/, '').length) {
			throw new Error('Proof attachment is outside the saved implementation; refresh the view.');
		}
		return start + position.character;
	};
	const insertions: Insertion[] = [];
	const seen = new Set<string>();
	const add = (insertion: Insertion) => {
		const key = JSON.stringify(insertion);
		if (!seen.has(key)) { insertions.push(insertion); seen.add(key); }
	};
	for (const contract of metadata.contracts) {
		if (contract.location.file !== root) continue;
		offset(contract.location.start);
		const line = contract.location.start.line;
		add({ offset: starts[line], indent: /^[\t ]*/.exec(lines[line])![0],
			kind: `Contract for ${contract.source} from`, body: contractBody(contract, readText), origin: contract.sourceLocation });
	}
	for (const step of metadata.steps) {
		if (step.location.file !== root) continue;
		add({ offset: offset(step.location.start), indent: /^[\t ]*/.exec(lines[step.location.start.line])![0],
			kind: 'Proof step from', body: step.text.trim(), origin: step.sourceLocation });
	}
	insertions.sort((a, b) => a.offset - b.offset);
	let text = '';
	let position: Position = { line: 0, character: 0 };
	const links: ProofViewResult['links'] = [];
	const append = (value: string) => {
		text += value;
		const last = value.lastIndexOf('\n');
		position = last < 0 ? { line: position.line, character: position.character + value.length }
			: { line: position.line + value.split('\n').length - 1, character: value.length - last - 1 };
	};
	const reference = (kind: string, origin: SourceLocation, indent = '') => {
		const file = (path.relative(workspace, origin.file) || path.basename(origin.file)).split(path.sep).join('/');
		append(`${indent}(* ${kind} `);
		const start = position;
		append(JSON.stringify(`${file}:${origin.start.line + 1}`));
		links.push({ range: { start, end: position }, target: URI.file(origin.file)
			.with({ fragment: `L${origin.start.line + 1},${origin.start.character + 1}` }).toString() });
		append(' *)\n');
	};
	const origin = (file: string): SourceLocation => ({ file, start: { line: 0, character: 0 }, end: { line: 0, character: 0 } });
	append('(* Caravan proof view — read-only. Follow source links to edit.\n');
	append('   External annotations appear at their implementation attachment points.\n');
	append('   Full companion files follow, including shared definitions and outline bindings.\n');
	append('   This assembled reading view is not a standalone verification input. *)\n\n');
	reference('Implementation:', origin(root));
	let cursor = 0;
	for (const insertion of insertions) {
		append(source.slice(cursor, insertion.offset));
		if (position.character !== 0) append('\n');
		reference(insertion.kind, insertion.origin, insertion.indent);
		append(`${insertion.indent}(*@ ${insertion.body.replace(/\n/g, `\n${insertion.indent}`)} *)\n`);
		if (insertion.offset > 0 && source[insertion.offset - 1] !== '\n') append(insertion.indent);
		cursor = insertion.offset;
	}
	append(source.slice(cursor));
	const stem = root.replace(/\.ml$/, '');
	const companions = new Set([`${stem}.mli`, `${stem}.proof`,
		...metadata.contracts.map(contract => contract.sourceLocation.file),
		...metadata.steps.map(step => step.sourceLocation.file)]);
	for (const file of companions) {
		if (file === root) continue;
		const content = readText(file);
		if (content === undefined) continue;
		append('\n\n');
		reference('Companion source:', origin(file));
		append(content);
	}
	return { text, links };
}
