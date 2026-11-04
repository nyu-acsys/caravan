import { spawn, execFile, type ChildProcess } from 'node:child_process';
import * as path from 'node:path';

const outputLimit = 4 * 1024 * 1024;
export interface ProcessResult { stdout: string; stderr: string; code: number | null }

/** Only an explicit rejection of --server permits a caller to retry in batch mode. */
export class UnsupportedServerError extends Error {}

function terminate(child: ChildProcess): void {
	if (child.pid === undefined) return;
	if (process.platform === 'win32') {
		execFile(path.join(process.env.SystemRoot ?? 'C:\\Windows', 'System32', 'taskkill.exe'),
			['/PID', String(child.pid), '/T', '/F'], { windowsHide: true }, () => {
				if (child.exitCode === null && child.signalCode === null) child.kill('SIGKILL');
			});
	} else {
		try { process.kill(-child.pid, 'SIGKILL'); }
		catch (error) {
			if ((error as NodeJS.ErrnoException).code !== 'ESRCH') child.kill('SIGKILL');
		}
	}
}

/** Bound concurrency; cancellation removes queued work and stops entire process groups. */
export class VerificationProcesses {
	private active = 0;
	private readonly queue: (() => void)[] = [];
	constructor(private readonly limit = 2) {
		if (!Number.isInteger(limit) || limit < 1) throw new Error('Invalid process limit');
	}
	private acquire(signal: AbortSignal): Promise<void> {
		return new Promise((resolve, reject) => {
			const start = () => {
				signal.removeEventListener('abort', abort);
				this.active++;
				resolve();
			};
			const abort = () => {
				const index = this.queue.indexOf(start);
				if (index >= 0) this.queue.splice(index, 1);
				reject(new Error('Verification cancelled'));
			};
			if (signal.aborted) abort();
			else if (this.active < this.limit) start();
			else {
				this.queue.push(start);
				signal.addEventListener('abort', abort, { once: true });
			}
		});
	}
	private async execute(executable: string, args: string[], cwd: string, signal: AbortSignal,
		env: NodeJS.ProcessEnv | undefined, input: boolean,
		listen: (child: ChildProcess, fail: (error: Error) => void) => (code: number | null) => ProcessResult): Promise<ProcessResult> {
		await this.acquire(signal);
		try {
			if (signal.aborted) throw new Error('Verification cancelled');
			return await new Promise<ProcessResult>((resolve, reject) => {
				const child = spawn(executable, args, {
					cwd, env, shell: false, detached: process.platform !== 'win32', windowsHide: true,
					stdio: [input ? 'pipe' : 'ignore', 'pipe', 'pipe']
				});
				let failure: Error | undefined;
				const fail = (error: Error) => { failure ??= error; terminate(child); };
				const abort = () => terminate(child);
				signal.addEventListener('abort', abort, { once: true });
				child.on('error', fail);
				// A rejected command may close stdin before reading the request.
				child.stdin?.on('error', error => {
					if ((error as NodeJS.ErrnoException).code !== 'EPIPE') fail(error);
				});
				const finish = listen(child, fail);
				child.on('close', code => {
					signal.removeEventListener('abort', abort);
					if (signal.aborted) reject(new Error('Verification cancelled'));
					else if (failure) reject(failure);
					else {
						try { resolve(finish(code)); } catch (error) { reject(error); }
					}
				});
			});
		} finally {
			this.active--;
			this.queue.shift()?.();
		}
	}
	async run(executable: string, args: string[], cwd: string, signal: AbortSignal, env?: NodeJS.ProcessEnv): Promise<ProcessResult> {
		return this.execute(executable, args, cwd, signal, env, false, (child, fail) => {
			const stdout: Buffer[] = [];
			const stderr: Buffer[] = [];
			let bytes = 0;
			const collect = (chunks: Buffer[], data: Buffer) => {
				bytes += data.length;
				if (bytes <= outputLimit) chunks.push(data);
				else fail(new Error('Caravan output exceeded 4 MiB'));
			};
			child.stdout!.on('data', (data: Buffer) => collect(stdout, data));
			child.stderr!.on('data', (data: Buffer) => collect(stderr, data));
			return code => ({ stdout: Buffer.concat(stdout).toString('utf8'), stderr: Buffer.concat(stderr).toString('utf8'), code });
		});
	}
	async serve(executable: string, prefixArgs: string[], args: string[], cwd: string,
		signal: AbortSignal, env: NodeJS.ProcessEnv | undefined,
		onPartial: (stdout: string, phase: 'typed' | 'scheduled' | 'progress') => void): Promise<ProcessResult> {
		return this.execute(executable, [...prefixArgs, '--server'], cwd, signal, env, true, (child, fail) => {
			const stderr: Buffer[] = [];
			let stderrBytes = 0;
			let line: Buffer[] = [];
			let lineBytes = 0;
			let validFrames = 0;
			let failed = false;
			let result: ProcessResult | undefined;
			const stop = (error: Error) => { failed = true; fail(error); };
			const frame = (data: Buffer) => {
				try {
					const value: unknown = JSON.parse(new TextDecoder('utf-8', { fatal: true }).decode(data));
					if (!value || typeof value !== 'object' || Array.isArray(value)) throw new Error('Invalid Caravan server frame');
					const message = value as Record<string, unknown>;
					if (message.id !== 1) throw new Error('Caravan server response ID mismatch');
					if (result) throw new Error('Caravan server frame after final response');
					if (typeof message.partial === 'string' &&
						(message.phase === 'typed' || message.phase === 'scheduled' || message.phase === 'progress') &&
						!('exit' in message) && !('stdout' in message) && !('stderr' in message)) {
						validFrames++;
						onPartial(message.partial, message.phase);
					} else if (Number.isSafeInteger(message.exit) && typeof message.stdout === 'string' &&
						typeof message.stderr === 'string' && !('partial' in message) && !('phase' in message)) {
						validFrames++;
						result = { stdout: message.stdout, stderr: message.stderr, code: message.exit as number };
					} else throw new Error('Invalid Caravan server frame');
				} catch (error) {
					stop(error instanceof Error ? error : new Error(String(error)));
				}
			};
			child.stdout!.on('data', (data: Buffer) => {
				let start = 0;
				while (start < data.length && !failed && !signal.aborted) {
					const newline = data.indexOf(10, start);
					const end = newline < 0 ? data.length : newline;
					lineBytes += end - start;
					if (lineBytes > outputLimit) { stop(new Error('Caravan server frame exceeded 4 MiB')); break; }
					line.push(data.subarray(start, end));
					if (newline < 0) break;
					frame(Buffer.concat(line, lineBytes));
					line = [];
					lineBytes = 0;
					start = newline + 1;
				}
			});
			child.stderr!.on('data', (data: Buffer) => {
				if (failed) return;
				stderrBytes += data.length;
				if (stderrBytes > outputLimit) stop(new Error('Caravan stderr exceeded 4 MiB'));
				else stderr.push(data);
			});
			child.stdin!.end(JSON.stringify({ id: 1, cwd, args, partial: true }) + '\n');
			return code => {
				const diagnostic = Buffer.concat(stderr).toString('utf8');
				const plainDiagnostic = diagnostic.replace(/\x1b\[[0-9;:]*m/g, '');
				if (lineBytes) throw new Error('Unterminated Caravan server frame');
				if (!validFrames && code !== 0 &&
					/\b(?:unknown|unrecognized)\s+option(?:\s*:\s*|\s+)[`'"]?--server(?:[`'".,:;!?]|\s|$)/i.test(plainDiagnostic)) {
					throw new UnsupportedServerError(diagnostic.trim());
				}
				if (code !== 0) throw new Error(`Caravan server exited ${code ?? 'without an exit code'}${diagnostic ? ': ' + diagnostic.trim() : ''}`);
				if (!result) throw new Error('Caravan server ended without a final response');
				if (Buffer.byteLength(result.stderr) + stderrBytes > outputLimit) throw new Error('Caravan stderr exceeded 4 MiB');
				return { ...result, stderr: result.stderr + diagnostic };
			};
		});
	}
}
