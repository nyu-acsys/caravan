#!/usr/bin/env python3
"""Serial, uncached Caravan emission and verification comparison.

Invoke inside the intended opam environment. This script never builds either
repository. Emission measures source loading/OCaml typing, Caravan translation,
and Raven pretty printing; it does not run Raven's verification pipeline.
Verification measures the end-to-end CLI path including Raven and the solver.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import signal
import statistics
import subprocess
import time


ROOT = Path(__file__).resolve().parents[3]


def parse_args():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT)
    parser.add_argument('--exe', type=Path, default=ROOT / '_build/default/bin/caravan.exe')
    parser.add_argument('--integer', type=Path,
                        default=ROOT / 'test/case_studies/striped_hash_set/striped_hash_set.ml')
    parser.add_argument('--generic', type=Path,
                        default=ROOT / 'test/case_studies/generic_striped_hash_set/generic_striped_hash_set.ml')
    parser.add_argument('--repetitions', type=int, default=5)
    parser.add_argument('--warmups', type=int, default=1)
    parser.add_argument('--timeout', type=float, default=300.0)
    parser.add_argument('--output-dir', type=Path)
    parser.add_argument('--include-dir', '-I', type=Path, action='append', default=[])
    parser.add_argument('--mode', choices=('both', 'emit', 'verify'), default='both')
    result = parser.parse_args()
    if result.repetitions < 1 or result.warmups < 0 or result.timeout <= 0:
        parser.error('repetitions must be positive, warmups nonnegative, and timeout positive')
    result.root = result.root.resolve()
    result.exe = result.exe.resolve()
    result.integer = result.integer.resolve()
    result.generic = result.generic.resolve()
    for source in (result.exe, result.integer, result.generic):
        if not source.is_file():
            parser.error(f'missing input: {source}')
    if result.output_dir is None:
        stamp = dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
        result.output_dir = Path('/tmp') / f'caravan-hashset-comparison-{stamp}'
    result.output_dir = result.output_dir.resolve()
    result.output_dir.mkdir(parents=True, exist_ok=False)
    return result


def snapshot(source):
    files = []
    for suffix in ('.ml', '.mli', '.proof'):
        path = source.with_suffix(suffix)
        if path.exists():
            data = path.read_bytes()
            files.append({'path': str(path), 'bytes': len(data),
                          'sha256': hashlib.sha256(data).hexdigest()})
    return files


def run_job(args, label, source, mode, phase, repetition):
    command = [str(args.exe), '--no-dune', '--shh', '--color=never']
    if mode == 'emit':
        command.append('--emit-rav')
    for directory in args.include_dir:
        command.extend(['-I', str(directory.resolve())])
    command.append(str(source))
    cpu_started = os.times()
    started = time.perf_counter()
    proc = subprocess.Popen(command, cwd=args.root, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, start_new_session=True)
    timed_out = False
    interrupted = False
    try:
        stdout, stderr = proc.communicate(timeout=args.timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(proc.pid, signal.SIGKILL)
        stdout, stderr = proc.communicate()
    except KeyboardInterrupt:
        interrupted = True
        os.killpg(proc.pid, signal.SIGKILL)
        stdout, stderr = proc.communicate()
    elapsed = time.perf_counter() - started
    cpu_finished = os.times()
    cpu_seconds = (cpu_finished.children_user + cpu_finished.children_system
                   - cpu_started.children_user - cpu_started.children_system)
    record = {
        'variant': label, 'source': str(source), 'mode': mode, 'phase': phase,
        'repetition': repetition, 'command': command, 'elapsed_seconds': elapsed,
        'process_tree_cpu_seconds': cpu_seconds,
        'returncode': proc.returncode, 'timed_out': timed_out,
        'interrupted': interrupted,
        'stdout_bytes': len(stdout), 'stderr_bytes': len(stderr),
        'stdout': stdout.decode('utf-8', errors='replace'),
        'stderr': stderr.decode('utf-8', errors='replace'),
    }
    if mode == 'emit' and proc.returncode == 0:
        emitted = args.output_dir / f'{label}-{phase}-{repetition}.rav'
        emitted.write_bytes(stdout)
        record['emitted_file'] = str(emitted)
    return record


def summarize(runs):
    summary = {}
    for mode in ('emit', 'verify'):
        by_variant = {}
        for label in ('integer', 'generic'):
            selected = [r for r in runs if r['mode'] == mode
                        and r['variant'] == label and r['phase'] == 'measured']
            if not selected:
                continue
            success = [r for r in selected if r['returncode'] == 0
                       and not r['timed_out'] and not r['interrupted']]
            values = [r['elapsed_seconds'] for r in success]
            item = {'runs': len(selected), 'successes': len(success),
                    'failures': len(selected) - len(success)}
            if values:
                item.update(median_seconds=statistics.median(values),
                            min_seconds=min(values), max_seconds=max(values))
                cpu_values = [r['process_tree_cpu_seconds'] for r in success]
                item.update(median_process_tree_cpu_seconds=statistics.median(cpu_values))
                if mode == 'emit':
                    sizes = [r['stdout_bytes'] for r in success]
                    item.update(emitted_bytes_min=min(sizes), emitted_bytes_max=max(sizes))
            by_variant[label] = item
        if by_variant:
            summary[mode] = by_variant
            if all('median_seconds' in by_variant.get(label, {})
                   for label in ('integer', 'generic')):
                summary[mode]['generic_over_integer_median'] = (
                    by_variant['generic']['median_seconds'] /
                    by_variant['integer']['median_seconds'])
    return summary


def main():
    args = parse_args()
    variants = [('integer', args.integer), ('generic', args.generic)]
    modes = ('emit', 'verify') if args.mode == 'both' else (args.mode,)
    manifest = {
        'created_utc': dt.datetime.now(dt.timezone.utc).isoformat(),
        'root': str(args.root), 'executable': str(args.exe),
        'executable_sha256': hashlib.sha256(args.exe.read_bytes()).hexdigest(),
        'inputs': {label: snapshot(path) for label, path in variants},
        'repetitions': args.repetitions, 'warmups': args.warmups,
        'timeout_seconds': args.timeout,
        'opam_switch_prefix': os.environ.get('OPAM_SWITCH_PREFIX'),
        'method': {
            'serial': True, 'verification_cache': 'disabled; no --cache-dir argument',
            'cpu': 'OS child user+system CPU time, including waited descendants on POSIX',
            'emit': 'CLI process startup + source loading/OCaml typing + Caravan translation + Raven printing; excludes Raven verification pipeline and SMT',
            'verify': 'CLI process startup + source loading/OCaml typing + Caravan translation + Raven verification pipeline + SMT',
            'ordering': 'Separate emit/verify phases; variants alternate within each repetition, order reversed on odd repetitions',
            'caveat': 'verify minus emit is not pure solver time: verification includes Raven preprocessing/SMT encoding while emission includes printing',
        },
        'runs': [],
    }
    result_path = args.output_dir / 'results.json'
    def save():
        manifest['summary'] = summarize(manifest['runs'])
        result_path.write_text(json.dumps(manifest, indent=2) + '\n')
    save()
    for mode in modes:
        for phase, count in (('warmup', args.warmups), ('measured', args.repetitions)):
            for repetition in range(count):
                order = variants if repetition % 2 == 0 else list(reversed(variants))
                for label, source in order:
                    record = run_job(args, label, source, mode, phase, repetition + 1)
                    manifest['runs'].append(record)
                    save()
                    print(f'{mode} {phase} {repetition + 1} {label}: '
                          f'{record["elapsed_seconds"]:.3f}s, exit {record["returncode"]}',
                          flush=True)
                    if record['interrupted']:
                        print(f'Interrupted; partial results saved to {result_path}', flush=True)
                        return 130
    print(json.dumps(manifest['summary'], indent=2), flush=True)
    print(f'Results: {result_path}', flush=True)
    return 0 if all(r['returncode'] == 0 for r in manifest['runs']) else 1


if __name__ == '__main__':
    raise SystemExit(main())
