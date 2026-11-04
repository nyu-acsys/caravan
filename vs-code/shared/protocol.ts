export const verificationStateNotification = 'caravan/verificationState';
export const verifyNotification = 'caravan/verify';

export type VerificationState = 'unchecked' | 'outdated' | 'verifying' | 'verified' | 'verifiedWithWarnings' | 'failed' | 'unavailable';
export interface VerificationStateParams {
	uri: string;
	version: number;
	state: VerificationState;
	message?: string;
}
export interface VerifyParams { uri: string }

export const toolchainNotification = 'caravan/toolchain';
export interface ToolchainSelection { executable: string; bundleRoot?: string }

export const openContractCommand = 'caravan.openContract';
export interface ContractLocation {
	uri: string;
	range: { start: { line: number; character: number }; end: { line: number; character: number } };
}

export const showProofViewCommand = 'caravan.showProofView';
export const proofViewScheme = 'caravan-proof-view';
export const proofViewRequest = 'caravan/proofView';
export const proofViewChangedNotification = 'caravan/proofViewChanged';
export interface ProofViewResult {
	text: string;
	links: { range: ContractLocation['range']; target: string }[];
}
