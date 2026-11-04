import type { CodeLens } from 'vscode-languageserver/node';
import type { VerificationState } from '../shared/protocol';
import type { MemberStatus, NormalizedMember } from './report';

const presentation: Record<MemberStatus, { glyph: string; words: string }> = {
	unchecked: { glyph: '○', words: 'not checked' },
	checked: { glyph: '○', words: 'type-checked' },
	trusted: { glyph: '–', words: 'trusted' },
	verified: { glyph: '✓', words: 'verified' },
	pending: { glyph: '⋯', words: 'checking' },
	skipped: { glyph: '–', words: 'skipped' },
	timeout: { glyph: '⏱', words: 'timed out' },
	failed: { glyph: '✗', words: 'failed' }
};

const summaryOrder: MemberStatus[] = ['failed', 'timeout', 'skipped', 'pending', 'verified', 'checked', 'trusted', 'unchecked'];
const rank: Record<MemberStatus, number> = {
	unchecked: 0, checked: 0, trusted: 0, verified: 1, pending: 2, skipped: 3, timeout: 4, failed: 5
};

function title(member: NormalizedMember, members: NormalizedMember[], state: VerificationState): string {
	if (state === 'outdated') return '○ outdated';
	if (state === 'unavailable') return '○ unavailable';
	const { glyph, words } = presentation[member.status];
	if (!member.group) return `${glyph} ${words}`;
	const counted = summaryOrder.filter(status => (member.counts[status] ?? 0) > 0);
	const parts = counted.map(status => `${member.counts[status]} ${presentation[status].words}`);
	const countedRank = Math.max(0, ...counted.map(status => rank[status]));
	if (rank[member.status] > Math.max(1, countedRank)) {
		const fileGate = members.some(candidate => candidate.kind === 'file' && candidate.ownChecks > 0
			&& rank[candidate.ownStatus] === rank[member.status]);
		const boundary = member.kind === 'file' || (fileGate && rank[member.ownStatus] < rank[member.status])
			? 'file' : member.kind.replace(/[-_]/g, ' ');
		parts.push(`${boundary} checks ${words}`);
	}
	if (parts.length === 0) return `${glyph} ${member.kind === 'file' ? `file checks ${words}` : words}`;
	return `${glyph} ${parts.join(', ')}`;
}

/** Source counts already exclude nested group summaries and generated obligations. */
export function memberLenses(members: NormalizedMember[], file: string, state: VerificationState): CodeLens[] {
	const seen = new Set<string>();
	const selected = members.filter(member => {
		if (member.location.file !== file || (member.kind === 'file' && member.ownChecks === 0) || seen.has(member.id)) return false;
		seen.add(member.id);
		return true;
	}).sort((left, right) => left.location.start.line - right.location.start.line
		|| left.location.start.character - right.location.start.character
		|| (left.id < right.id ? -1 : left.id > right.id ? 1 : 0));
	return selected.map(member => ({
		range: { start: member.location.start, end: member.location.start },
		command: { command: '', title: title(member, members, state) }
	}));
}
