import { URI } from 'vscode-uri';
import type { InlayHint, Range } from 'vscode-languageserver/node';
import type { NormalizedProofStep, Position } from './report';
import { annotationMarkdown } from './contracts';

function before(left: Position, right: Position): boolean {
	return left.line < right.line || (left.line === right.line && left.character < right.character);
}

function label(text: string): string {
	const body = text.trim().replace(/^proof\s+/, '').replace(/\s+/g, ' ');
	if (/^(?:Ghost\.(?:State\.)?scope\b|begin\b|\(?fun\b)/.test(body)) return 'proof';
	if (Array.from(body).length <= 64) return body || 'proof';
	const head = /^[A-Za-z_][A-Za-z0-9_'.]*/.exec(body)?.[0] ?? 'proof';
	return `${head.slice(0, 62)} …`;
}

export function proofHints(steps: NormalizedProofStep[], root: string, range: Range, workspace: string): InlayHint[] {
	const seen = new Set<string>();
	const hints: InlayHint[] = [];
	for (const step of steps) {
		const position = step.location.start;
		if (step.location.file !== root || !step.sourceLocation.file.endsWith('.proof')
			|| before(position, range.start) || before(range.end, position)) continue;
		const key = JSON.stringify([step.location, step.sourceLocation, step.text]);
		if (seen.has(key)) continue;
		seen.add(key);
		hints.push({ position, paddingLeft: true, paddingRight: true,
			label: [{ value: label(step.text), location: { uri: URI.file(step.sourceLocation.file).toString(),
				range: { start: step.sourceLocation.start, end: step.sourceLocation.end } } }],
			tooltip: annotationMarkdown('Proof step', step.text.trim(), step.sourceLocation, workspace) });
	}
	return hints.sort((left, right) => left.position.line - right.position.line || left.position.character - right.position.character);
}
