import { spawn, execFile, type ChildProcess } from 'node:child_process';
import * as path from 'node:path';

const outputLimit = 4 * 1024 * 1024;
export interface ProcessResult { stdout: string; stderr: string; code: number | null }

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
	async run(executable: string, args: string[], cwd: string, signal: AbortSignal): Promise<ProcessResult> {
		await this.acquire(signal);
		try {
			if (signal.aborted) throw new Error('Verification cancelled');
			return await new Promise<ProcessResult>((resolve, reject) => {
				const child = spawn(executable, args, {
					cwd, shell: false, detached: process.platform !== 'win32', windowsHide: true,
					stdio: ['ignore', 'pipe', 'pipe']
				});
				const stdout: Buffer[] = [];
				const stderr: Buffer[] = [];
				let bytes = 0;
				let failure: Error | undefined;
				const abort = () => terminate(child);
				signal.addEventListener('abort', abort, { once: true });
				const collect = (chunks: Buffer[], data: Buffer) => {
					bytes += data.length;
					if (bytes <= outputLimit) chunks.push(data);
					else { failure ??= new Error('Caravan output exceeded 4 MiB'); terminate(child); }
				};
				child.stdout.on('data', (data: Buffer) => collect(stdout, data));
				child.stderr.on('data', (data: Buffer) => collect(stderr, data));
				child.on('error', error => { failure = error; });
				child.on('close', code => {
					signal.removeEventListener('abort', abort);
					if (signal.aborted) reject(new Error('Verification cancelled'));
					else if (failure) reject(failure);
					else resolve({ stdout: Buffer.concat(stdout).toString('utf8'), stderr: Buffer.concat(stderr).toString('utf8'), code });
				});
			});
		} finally {
			this.active--;
			this.queue.shift()?.();
		}
	}
}
