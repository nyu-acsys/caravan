"""Dependency-free Windows bundle checks; run with python -m unittest discover -s scripts/release."""
import os
from pathlib import Path
import struct
import tempfile
import unittest
from unittest.mock import patch

import bundle


def image(imports=(), delayed=()):
    data = bytearray(4096)
    data[:2] = b'MZ'
    struct.pack_into('<I', data, 0x3c, 0x80)
    data[0x80:0x84] = b'PE\0\0'
    struct.pack_into('<HH', data, 0x84, 0x8664, 1)
    struct.pack_into('<H', data, 0x94, 240)
    optional = 0x98
    struct.pack_into('<H', data, optional, 0x20b)
    struct.pack_into('<Q', data, optional + 24, 0x140000000)
    struct.pack_into('<I', data, optional + 60, 512)
    struct.pack_into('<I', data, optional + 108, 16)
    struct.pack_into('<IIII', data, optional + 240 + 8, 3584, 0x1000, 3584, 512)
    name_offset = 2048
    for directory, names, offset, size in [(1, imports, 512, 20), (13, delayed, 1024, 32)]:
        if not names:
            continue
        struct.pack_into('<II', data, optional + 112 + directory * 8,
                         offset + 0xe00, (len(names) + 1) * size)
        for index, name in enumerate(names):
            encoded = name.encode('ascii') + b'\0'
            data[name_offset:name_offset + len(encoded)] = encoded
            descriptor = offset + index * size
            if directory == 1:
                struct.pack_into('<I', data, descriptor + 12, name_offset + 0xe00)
            else:
                struct.pack_into('<II', data, descriptor, 1, name_offset + 0xe00)
            name_offset += len(encoded)
    return data


class WindowsBundleTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        for name in ['source', 'runtime', 'output', 'Windows/System32']:
            (self.root / name).mkdir(parents=True)

    def write(self, name, imports=(), delayed=()):
        path = self.root / name
        path.write_bytes(image(imports, delayed))
        return path

    def collect(self, executable):
        return bundle.collect_windows_dlls([executable], self.root / 'output',
                                           [self.root / 'runtime'], self.root / 'Windows')

    def test_normal_and_delayed_imports(self):
        executable = self.write('source/app.exe', ['KERNEL32.dll'], ['runtime.dll'])
        self.assertEqual(bundle.pe_imports(executable), ['KERNEL32.dll', 'runtime.dll'])

    def test_recursive_dependencies_and_system_exclusion(self):
        executable = self.write('source/app.exe', ['Runtime.DLL', 'KERNEL32.dll', 'api-ms-win-core-test.dll'])
        self.write('runtime/runtime.dll', delayed=['nested.dll'])
        self.write('runtime/nested.dll', ['RUNTIME.dll'])
        (self.root / 'Windows/System32/kernel32.dll').write_bytes(b'system')
        copied = self.collect(executable)
        self.assertEqual(set(copied), {'runtime.dll', 'nested.dll'})
        self.assertEqual(len(list((self.root / 'output').iterdir())), 2)

    def test_system32_redistributable_is_bundled(self):
        executable = self.write('source/app.exe', ['VCRUNTIME140.dll'])
        self.write('Windows/System32/vcruntime140.dll')
        self.assertEqual(set(self.collect(executable)), {'vcruntime140.dll'})
        self.assertTrue((self.root / 'output/VCRUNTIME140.dll').is_file())

    def test_windows_cpp_system_library_is_not_bundled(self):
        executable = self.write('source/app.exe', ['msvcp_win.dll', 'msvcrt.dll'])
        for name in ['msvcp_win.dll', 'msvcrt.dll']:
            (self.root / 'Windows/System32' / name).write_bytes(b'system')
        self.assertEqual(self.collect(executable), {})

    def test_runtime_notices_required_and_copied_as_regular_files(self):
        with self.assertRaisesRegex(ValueError, 'require license notices'):
            bundle.collect_runtime_notices([], self.root / 'output', required=True)
        notices = self.root / 'documentation'
        (notices / 'gcc').mkdir(parents=True)
        (notices / 'gcc/COPYING.RUNTIME').write_text('Runtime license')
        (notices / 'gcc/README').write_text('Not a license notice')
        self.assertEqual(bundle.collect_runtime_notices([notices], self.root / 'output',
                                                       required=True), 1)
        target = self.root / 'output/documentation/gcc/COPYING.RUNTIME'
        self.assertEqual(target.read_text(), 'Runtime license')
        self.assertFalse(target.is_symlink())

    def test_unresolved_dependency_fails(self):
        executable = self.write('source/app.exe', ['missing.dll'])
        with self.assertRaisesRegex(ValueError, 'Unresolved Windows dependency'):
            self.collect(executable)

    def test_wrong_architecture_and_truncated_image_fail(self):
        executable = self.write('source/app.exe')
        data = bytearray(executable.read_bytes())
        struct.pack_into('<H', data, 0x84, 0x14c)
        executable.write_bytes(data)
        with self.assertRaisesRegex(ValueError, 'x64 PE'):
            bundle.pe_imports(executable)
        executable.write_bytes(b'MZ')
        with self.assertRaisesRegex(ValueError, 'Truncated PE'):
            bundle.pe_imports(executable)

    def test_unmapped_and_unterminated_import_directory_fail(self):
        executable = self.write('source/app.exe', ['runtime.dll'])
        data = bytearray(executable.read_bytes())
        struct.pack_into('<I', data, 512 + 12, 0xdeadbeef)
        executable.write_bytes(data)
        with self.assertRaisesRegex(ValueError, 'Unmapped PE address'):
            bundle.pe_imports(executable)
        data = image(['runtime.dll'])
        struct.pack_into('<I', data, 0x98 + 112 + 8 + 4, 20)
        executable.write_bytes(data)
        with self.assertRaisesRegex(ValueError, 'Unterminated PE import directory'):
            bundle.pe_imports(executable)

    def test_unsafe_import_fails(self):
        executable = self.write('source/app.exe', ['../evil.dll'])
        with self.assertRaisesRegex(ValueError, 'Unsafe PE import'):
            bundle.pe_imports(executable)

    def test_conflicting_flattened_dependencies_fail(self):
        (self.root / 'other').mkdir()
        executable = self.write('source/app.exe', ['a.dll', 'b.dll'])
        self.write('runtime/a.dll', ['same.dll'])
        self.write('source/b.dll', ['same.dll'])
        self.write('source/same.dll')
        self.write('runtime/same.dll', ['extra.dll'])
        with self.assertRaisesRegex(ValueError, 'Conflicting Windows dependency'):
            self.collect(executable)

    def test_windows_smoke_environment_has_no_toolchain_path(self):
        with patch.dict(os.environ, {'SystemRoot': str(self.root / 'Windows'),
                                     'PATH': '/opam/bin', 'Path': '/other-opam/bin', 'OPAM_SWITCH_PREFIX': '/opam',
                                     'CAML_LD_LIBRARY_PATH': '/opam/lib'}, clear=True):
            environment = bundle.smoke_environment(self.root / 'output', self.root, True)
        self.assertEqual(environment['PATH'].split(os.pathsep),
                         [str(self.root / 'output'), str(self.root / 'Windows/System32'),
                          str(self.root / 'Windows')])
        self.assertNotIn('Path', environment)
        self.assertNotIn('OPAM_SWITCH_PREFIX', environment)
        self.assertNotIn('CAML_LD_LIBRARY_PATH', environment)
        self.assertFalse(Path(environment['OCAMLLIB']).exists())


if __name__ == '__main__':
    unittest.main()
