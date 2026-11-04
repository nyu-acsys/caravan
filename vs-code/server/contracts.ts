import * as path from 'node:path';
import { URI } from 'vscode-uri';
import type { CodeLens } from 'vscode-languageserver/node';
import { openContractCommand, type ContractLocation } from '../shared/protocol';
import type { NormalizedContract } from './report';

export function contractLenses(contracts: NormalizedContract[], root: string): CodeLens[] {
	const seen = new Set<string>();
	const lenses: CodeLens[] = [];
	for (const contract of contracts) {
		if (contract.location.file !== root || !/\.(mli|proof)$/.test(contract.sourceLocation.file)) continue;
		const key = JSON.stringify([contract.location, contract.sourceLocation]);
		if (seen.has(key)) continue;
		seen.add(key);
		const clauses = contract.clauses.map(clause => `${clause.keyword} ${clause.text}`);
		const summary = clauses.join(' · ').replace(/\s+/g, ' ').trim();
		const prefix = `contract (${path.basename(contract.sourceLocation.file)})`;
		const characters = Array.from(summary);
		const brief = characters.length > 120 ? `${characters.slice(0, 119).join('')}…` : summary;
		const title = summary ? `${prefix}: ${brief}` : prefix;
		const origin: ContractLocation = { uri: URI.file(contract.sourceLocation.file).toString(),
			range: { start: contract.sourceLocation.start, end: contract.sourceLocation.end } };
		const command = {
			title,
			command: openContractCommand, arguments: [origin]
		};
		lenses.push({ range: { start: contract.location.start, end: contract.location.start }, command });
	}
	return lenses;
}
