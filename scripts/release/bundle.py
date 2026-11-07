#!/usr/bin/env python3
"""Build a relocatable native bundle, then verify the extracted archive."""
import argparse
import hashlib
import json
import os
import platform
import re
from pathlib import Path
import shutil
import subprocess
import struct
import tarfile
import tempfile


def run(*args, **kwargs):
    return subprocess.check_output(args, text=True, **kwargs)


def pe_imports(path):
    """Read x64 PE import names, including eagerly packaged delay imports."""
    data = Path(path).read_bytes()

    def unpack(fmt, offset):
        if offset < 0 or offset + struct.calcsize(fmt) > len(data):
            raise ValueError(f'Truncated PE image: {path}')
        return struct.unpack_from(fmt, data, offset)

    if data[:2] != b'MZ':
        raise ValueError(f'Not a PE image: {path}')
    pe, = unpack('<I', 0x3c)
    if data[pe:pe + 4] != b'PE\0\0':
        raise ValueError(f'Invalid PE signature: {path}')
    machine, section_count = unpack('<HH', pe + 4)
    optional_size, = unpack('<H', pe + 20)
    optional = pe + 24
    magic, = unpack('<H', optional)
    if machine != 0x8664 or magic != 0x20b:
        raise ValueError(f'Expected an x64 PE image: {path}')
    image_base, = unpack('<Q', optional + 24)
    header_size, = unpack('<I', optional + 60)
    directory_count, = unpack('<I', optional + 108)
    sections = []
    for index in range(section_count):
        offset = optional + optional_size + 40 * index
        virtual_size, address, raw_size, raw_offset = unpack('<IIII', offset + 8)
        sections.append((address, virtual_size, raw_offset, raw_size))

    def file_offset(rva, size=1):
        if rva < header_size and rva + size <= min(header_size, len(data)):
            return rva
        for address, virtual_size, raw_offset, raw_size in sections:
            delta = rva - address
            if 0 <= delta and delta + size <= raw_size:
                offset = raw_offset + delta
                if offset + size <= len(data):
                    return offset
        raise ValueError(f'Unmapped PE address in {path}')

    def name_at(rva):
        offset = file_offset(rva)
        end = data.find(b'\0', offset, offset + 1024)
        if end < 0:
            raise ValueError(f'Unterminated PE import in {path}')
        name = data[offset:end].decode('ascii')
        if not re.fullmatch(r'[A-Za-z0-9_.+-]+\.dll', name, re.IGNORECASE):
            raise ValueError(f'Unsafe PE import name {name!r} in {path}')
        return name

    names = set()
    for directory, descriptor_size in [(1, 20), (13, 32)]:
        if directory >= directory_count:
            continue
        if 112 + (directory + 1) * 8 > optional_size:
            raise ValueError(f'Invalid PE directory table: {path}')
        address, size = unpack('<II', optional + 112 + directory * 8)
        if not address:
            continue
        terminated = False
        for relative in range(0, size - descriptor_size + 1, descriptor_size):
            descriptor = unpack('<' + 'I' * (descriptor_size // 4),
                                file_offset(address + relative, descriptor_size))
            if not any(descriptor):
                terminated = True
                break
            name_rva = descriptor[3] if directory == 1 else descriptor[1]
            if directory == 13 and not descriptor[0] & 1:
                name_rva -= image_base
            names.add(name_at(name_rva))
        if not terminated:
            raise ValueError(f'Unterminated PE import directory: {path}')
    return sorted(names, key=str.lower)


def collect_windows_dlls(executables, destination, search_paths, system_root):
    """Copy the reachable non-system DLL closure beside the bundled executables."""
    system_directory = Path(system_root) / 'System32'

    def lookup(directory, name):
        if directory.is_dir():
            return next((p for p in sorted(directory.iterdir())
                         if p.is_file() and p.name.lower() == name.lower()), None)
        return None

    pending = [Path(p).resolve() for p in executables]
    copied = {}
    visited = set()
    while pending:
        source = pending.pop()
        if source in visited:
            continue
        visited.add(source)
        for name in pe_imports(source):
            # API sets are virtual Windows loader contracts, not distributable files.
            if name.lower().startswith(('api-ms-win-', 'ext-ms-win-')):
                continue
            redistributable = re.match(r'(?:vcruntime|msvcp|msvcr|concrt|vcomp)\d',
                                      name, re.IGNORECASE) is not None
            if not redistributable and lookup(system_directory, name):
                continue
            directories = [source.parent] + [Path(p) for p in search_paths]
            if redistributable:
                directories.append(system_directory)
            dependency = next((found for directory in directories
                               if (found := lookup(directory, name))), None)
            if dependency is None:
                raise ValueError(f'Unresolved Windows dependency {name} imported by {source}')
            dependency = dependency.resolve()
            key = name.lower()
            if key in copied:
                if copied[key].read_bytes() != dependency.read_bytes():
                    raise ValueError(f'Conflicting Windows dependency {name}')
                continue
            copied[key] = dependency
            shutil.copyfile(dependency, Path(destination) / name)
            pending.append(dependency)
    return copied


def collect_runtime_notices(roots, destination, required=False):
    """Preserve toolchain license notices as regular files in the bundle."""
    count = 0
    labels = set()
    for root in roots:
        root = Path(root)
        label = root.name
        if label in labels:
            raise ValueError(f'Duplicate runtime notice root label: {label}')
        labels.add(label)
        if not root.is_dir():
            raise ValueError(f'Runtime notice directory does not exist: {root}')
        for source in sorted(root.rglob('*')):
            if source.is_file() and source.name.lower().startswith(
                    ('license', 'licence', 'copying', 'copyright', 'notice')):
                target = Path(destination) / label / source.relative_to(root)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, target)
                count += 1
    if required and count == 0:
        raise ValueError('Bundled Windows runtime DLLs require license notices; '
                         'pass --runtime-notices with a toolchain documentation directory')
    return count


def smoke_environment(binary_directory, temporary, windows=False):
    environment = {key: value for key, value in os.environ.items()
                   if key.upper() != 'PATH'
                   and not key.upper().startswith(('OPAM', 'OCAML', 'CAML'))}
    environment['OCAMLLIB'] = str(Path(temporary) / 'missing-stdlib')
    if windows:
        system_root = Path(os.environ['SystemRoot'])
        paths = [str(binary_directory), str(system_root / 'System32'), str(system_root)]
    else:
        paths = [str(binary_directory), '/usr/bin', '/bin']
    environment['PATH'] = os.pathsep.join(paths)
    return environment


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--platform', choices=['linux-x64', 'darwin-arm64', 'win32-x64'], required=True)
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--z3-root', type=Path, required=True)
    parser.add_argument('--ocaml-license', type=Path, required=True)
    parser.add_argument('--raven-license', type=Path, required=True)
    parser.add_argument('--output', type=Path, default=Path('dist'))
    parser.add_argument('--tag')
    parser.add_argument('--ocamlc', default='ocamlc')
    parser.add_argument('--stdlib', type=Path)
    parser.add_argument('--opam-doc', type=Path)
    parser.add_argument('--runtime-notices', type=Path, action='append', default=[])
    args = parser.parse_args()
    native_target = {('Linux', 'x86_64'): 'linux-x64', ('Darwin', 'arm64'): 'darwin-arm64',
                     ('Windows', 'amd64'): 'win32-x64', ('Windows', 'x86_64'): 'win32-x64'}.get(
        (platform.system(), platform.machine().lower()))
    if args.platform != native_target:
        parser.error('The bundle target must match the native build machine')
    manifest = json.loads(run(str(args.binary.resolve()), '--manifest'))
    required = {'version', 'lsp_protocol', 'min_z3', 'ocaml_version', 'raven_api_version'}
    if not required <= manifest.keys():
        raise ValueError('Binary manifest lacks required compatibility fields')
    if args.tag and args.tag != 'v' + manifest['version']:
        raise ValueError('Release tag does not match the binary version')
    compiler_version = run(args.ocamlc, '-version').strip()
    if compiler_version != manifest['ocaml_version']:
        raise ValueError('The bundle compiler differs from the binary compiler')
    stdlib = args.stdlib or Path(run(args.ocamlc, '-where').strip())
    documentation = args.opam_doc or Path(run('opam', 'var', 'doc').strip())
    windows = args.platform == 'win32-x64'
    extension = '.exe' if windows else ''
    z3_binary = args.z3_root / 'bin' / ('z3' + extension)
    args.output.mkdir(parents=True, exist_ok=True)
    archive = args.output / f'caravan-{args.platform}.tar.gz'
    with tempfile.TemporaryDirectory(prefix='caravan-bundle-') as temporary:
        staging = Path(temporary) / 'staging'
        (staging / 'bin').mkdir(parents=True)
        (staging / 'lib/ocaml').mkdir(parents=True)
        (staging / 'licenses').mkdir()
        for source, name in [(args.binary, 'caravan' + extension), (z3_binary, 'z3' + extension)]:
            shutil.copyfile(source, staging / 'bin' / name)
            (staging / 'bin' / name).chmod(0o755)
        if windows:
            search_paths = [args.binary.resolve().parent, z3_binary.resolve().parent]
            search_paths.extend(Path(p) for p in os.environ.get('PATH', '').split(os.pathsep) if p)
            runtime_dlls = collect_windows_dlls(
                [args.binary, z3_binary], staging / 'bin', search_paths, os.environ['SystemRoot'])
            collect_runtime_notices(args.runtime_notices, staging / 'licenses/runtime',
                                    required=bool(runtime_dlls))
        elif args.runtime_notices:
            collect_runtime_notices(args.runtime_notices, staging / 'licenses/runtime')
        interfaces = sorted(p for p in stdlib.rglob('*.cmi')
                            if 'compiler-libs' not in p.relative_to(stdlib).parts)
        if not interfaces:
            raise ValueError('Compiler standard library contains no interfaces')
        for source in interfaces:
            destination = staging / 'lib/ocaml' / source.relative_to(stdlib)
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, destination)
        shutil.copyfile('LICENSE', staging / 'licenses/Caravan-LICENSE')
        shutil.copyfile(args.raven_license, staging / 'licenses/Raven-LICENSE')
        shutil.copyfile(args.ocaml_license, staging / 'licenses/OCaml-LICENSE')
        for source in sorted(documentation.rglob('*')):
            if source.is_file() and source.name.lower().startswith(
                    ('license', 'licence', 'copying', 'copyright', 'notice')):
                destination = staging / 'licenses/opam' / source.relative_to(documentation)
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(source, destination)
        z3_licenses = [p for p in args.z3_root.iterdir() if p.is_file() and p.name.lower().startswith(('license', 'licence'))]
        if not z3_licenses:
            raise ValueError('Z3 distribution has no license')
        for source in z3_licenses:
            shutil.copyfile(source, staging / 'licenses' / ('Z3-' + source.name))
        manifest_text = json.dumps(manifest, sort_keys=True, indent=2) + '\n'
        (staging / 'manifest.json').write_text(manifest_text)
        with tarfile.open(archive, 'w:gz', format=tarfile.USTAR_FORMAT) as output:
            for entry in sorted(staging.iterdir()):
                output.add(entry, arcname=entry.name)
        # Move away from staging and override the compiler installation's environment.
        relocated = Path(temporary) / 'relocated'
        relocated.mkdir()
        with tarfile.open(archive) as packed:
            packed.extractall(relocated, filter='data')
        shutil.rmtree(staging)
        smoke = Path(temporary) / 'smoke.ml'
        smoke.write_text('let identity (x : int) = x\n')
        environment = smoke_environment(relocated / 'bin', temporary, windows)
        z3_version = run(str(relocated / 'bin' / ('z3' + extension)), '--version', env=environment)
        match = re.search(r'\b(\d+)\.(\d+)\.(\d+)\b', z3_version)
        minimum = tuple(int(part) for part in manifest['min_z3'].split('.'))
        if not match or tuple(map(int, match.groups())) < minimum:
            raise ValueError('Bundled Z3 does not satisfy manifest.min_z3')
        relocated_manifest = json.loads(run(str(relocated / 'bin' / ('caravan' + extension)), '--manifest',
                                            env=environment))
        if relocated_manifest != manifest:
            raise ValueError('Relocated executable manifest differs from bundle manifest')
        run(str(relocated / 'bin' / ('caravan' + extension)), '--shh', str(smoke), env=environment, cwd=temporary)
        (args.output / 'manifest.json').write_text(manifest_text)
    checksums = []
    for artifact in [archive, args.output / 'manifest.json']:
        with artifact.open('rb') as source:
            digest = hashlib.file_digest(source, 'sha256').hexdigest()
        checksums.append(f'{digest}  {artifact.name}\n')
    (args.output / 'SHA256SUMS').write_text(''.join(checksums))


if __name__ == '__main__':
    main()
