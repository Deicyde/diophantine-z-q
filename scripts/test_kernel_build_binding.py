import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from kernel_build_binding import bind_external_lookups, bind_project_lookups, collect_bound_inventory


def row(owner, path, sha='a', size=1):
    return {'owner': owner, 'path': path, 'sha256': sha*64, 'size': size}


class BindingTests(unittest.TestCase):
    def setUp(self):
        self.packages = {'packages': {'dep': {'type': 'git', 'location': '.lake/packages/dep',
                                           'revision': 'c'*40}}}
        self.compiler = {'builtins': {'Init': {'compiled_path': 'lib/lean/Init.olean',
                                              'compiled_sha256': 'a'*64}},
                         'files': {'lib/lean/Init.olean': {'sha256': 'a'*64, 'size': 1}}}
        self.files = {'dep': {'Dep.lean': {'sha256': 'b'*64, 'size': 2},
                             '.lake/build/lib/lean/Dep.olean': {'sha256': 'a'*64, 'size': 1}}}
        self.lookups = {
            'Init': {'source': row('toolchain', 'src/lean/Init.lean'),
                     'compiled': row('toolchain', 'lib/lean/Init.olean')},
            'Dep': {'source': row('workspace', '.lake/packages/dep/Dep.lean', 'b', 2),
                    'compiled': row('workspace', '.lake/packages/dep/.lake/build/lib/lean/Dep.olean')}}

    def bind(self):
        return bind_external_lookups(self.lookups, self.packages, self.compiler, self.files)

    def test_actual_compiled_and_source_bytes_are_bound_to_one_package(self):
        external, builtin = self.bind()
        self.assertEqual(external['Dep']['revision'], 'c'*40)
        self.assertEqual(external['Dep']['compiled_sha256'], 'a'*64)
        self.assertEqual(builtin['Init']['compiled_path'], 'lib/lean/Init.olean')

    def test_poisoned_or_unrecorded_compiled_file_is_rejected(self):
        for mutate in ('changed-hash', 'unrecorded-path', 'changed-size'):
            with self.subTest(mutate=mutate):
                saved = copy.deepcopy(self.lookups)
                item = self.lookups['Dep']['compiled']
                if mutate == 'changed-hash': item['sha256'] = 'e'*64
                elif mutate == 'unrecorded-path': item['path'] += '.other'
                else: item['size'] = 999
                with self.assertRaisesRegex(ValueError, 'fingerprinted'):
                    self.bind()
                self.lookups = saved

    def test_workspace_shadow_or_cross_package_source_is_rejected(self):
        for name, owner, path in (
                ('Init', 'workspace', 'Init.lean'),
                ('Dep', 'workspace', 'Dep.lean'),
                ('Dep', 'workspace', '.lake/packages/other/Dep.lean')):
            with self.subTest(name=name, path=path):
                saved = copy.deepcopy(self.lookups)
                self.lookups[name]['source'] = row(owner, path)
                with self.assertRaises(ValueError): self.bind()
                self.lookups = saved

    def test_overlapping_package_roots_do_not_make_ownership_ambiguous(self):
        self.packages['packages']['parent'] = {'type': 'git', 'location': '.lake/packages',
                                              'revision': 'd'*40}
        with self.assertRaisesRegex(ValueError, 'unique pinned'):
            self.bind()

    def test_alias_names_and_alias_input_paths_are_rejected(self):
        for name in ('dep', 'Different'):
            with self.subTest(name=name):
                self.lookups[name] = copy.deepcopy(self.lookups['Dep'])
                with self.assertRaisesRegex(ValueError, 'aliased|Aliased'):
                    self.bind()
                del self.lookups[name]

    def test_project_source_lookup_is_exact_and_compiled_output_optional_before_build(self):
        paths = {'Project.A': {'source_path': 'Project/A.lean',
                              'lean_output_prefix': '.lake/build/lib/lean/Project/A'}}
        lookups = {'Project.A': {'source': row('workspace', 'Project/A.lean')}}
        self.assertEqual(bind_project_lookups(lookups, paths), paths)
        lookups['Project.A']['compiled'] = row('workspace', '.lake/build/lib/lean/Project/A.olean')
        self.assertEqual(bind_project_lookups(lookups, paths), paths)
        lookups['Project.A']['compiled']['path'] = '.lake/packages/shadow/Project/A.olean'
        with self.assertRaisesRegex(ValueError, 'compiled lookup'):
            bind_project_lookups(lookups, paths)
        with self.assertRaisesRegex(ValueError, 'exact contract'):
            bind_project_lookups({}, paths)

    def test_collector_connects_exact_source_header_and_lookup(self):
        self.run_collector_fixture(mutate=False)

    def test_collector_rejects_source_changed_after_header_parsing(self):
        self.run_collector_fixture(mutate=True)

    def run_collector_fixture(self, *, mutate):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root/'lake-manifest.json').write_text(json.dumps({'packages': []}))
            (root/'lakefile.toml').write_text('name="fixture"\n[[lean_lib]]\nname="Project"\n')
            source = root/'Project.lean'
            source.write_text('prelude\n')
            header = {'isModule': False, 'imports': []}
            def query(*args, **kwargs):
                if mutate:
                    source.write_text('prelude\n-- changed after parser observation\n')
                return {'Project': {'source': 'Project.lean', 'imports': [], 'header': header}}
            def lookup(*args, **kwargs):
                raw = source.read_bytes()
                return {'Project': {'source': {'owner': 'workspace', 'path': 'Project.lean',
                    'sha256': hashlib.sha256(raw).hexdigest(), 'size': len(raw)}}}
            with patch('kernel_build_inventory.query_headers', side_effect=query), \
                    patch('kernel_build_resolution.resolve_imports', side_effect=lookup):
                args = (root, root/'toolchain', {'Project': 'Project.lean'},
                        self.packages, self.compiler, self.files, {})
                if mutate:
                    with self.assertRaisesRegex(ValueError, 'changed while parsing'):
                        collect_bound_inventory(*args)
                else:
                    inventory, binding = collect_bound_inventory(*args)
                    self.assertEqual(inventory['Project']['inputs']['header'], header)
                    self.assertEqual(binding['project_resolution']['Project']['source_path'], 'Project.lean')


if __name__ == '__main__':
    unittest.main()
