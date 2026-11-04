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
