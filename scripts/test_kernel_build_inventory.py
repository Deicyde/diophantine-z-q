import copy
from pathlib import Path
import tempfile
import unittest

import kernel_build_inventory as inventory


def header(*names):
    return {'isModule': False, 'imports': [{'module': n, 'isMeta': False,
            'isExported': True, 'importAll': False} for n in names]}


class InventoryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root/'A.lean').write_text('import B\n', encoding='utf-8')
        (self.root/'B.lean').write_text('def b := 1\n', encoding='utf-8')
        self.paths = {'A': 'A.lean', 'B': 'B.lean'}
        self.builtins = {'Init': {'compiled_path': 'lib/lean/Init.olean', 'compiled_sha256': 'a'*64}}
        self.rows = {
            'A': {'source': str(self.root/'A.lean'), 'imports': ['B'], 'header': header('Init', 'B')},
            'B': {'source': str(self.root/'B.lean'), 'imports': [], 'header': header('Init')}}

    def collect(self, query=None, external=None):
        return inventory.collect(self.root, self.paths, external or {}, self.builtins,
                                  query=query or (lambda root, names: copy.deepcopy(self.rows)))

    def test_exact_source_and_compiler_imports_are_recorded(self):
        result = self.collect()
        self.assertEqual(result['A']['inputs']['project_imports'], ['B'])
        self.assertEqual(result['B']['inputs']['builtin_imports'], self.builtins)
        self.assertEqual(result['A']['inputs']['source_sha256'], inventory.read_source(self.root, 'A.lean'))

    def test_wrong_source_resolution_is_not_accepted_as_the_contract_module(self):
        self.rows['A']['source'] = str(self.root/'B.lean')
        with self.assertRaisesRegex(ValueError, 'source resolution'):
            self.collect()

    def test_unresolved_external_and_missing_project_import_fail(self):
        self.rows['A']['imports'].append('Unknown')
        self.rows['A']['header'] = header('Init', 'B', 'Unknown')
        with self.assertRaisesRegex(ValueError, 'Unresolved external'):
            self.collect()
        self.rows['A']['imports'] = []
        self.rows['A']['header'] = header('Init', 'B')
        with self.assertRaisesRegex(ValueError, 'facets disagree'):
            self.collect()

    def test_external_package_identity_is_bound_in_the_input_record(self):
        self.rows['A']['imports'] = ['B', 'Mathlib.Example']
        self.rows['A']['header'] = header('Init', 'B', 'Mathlib.Example')
        external = {'Mathlib.Example': {'package': 'mathlib', 'revision': 'f'*40,
                    'source_path': '.lake/packages/mathlib/Mathlib/Example.lean',
                    'source_sha256': 'e'*64}}
        self.assertEqual(self.collect(external=external)['A']['inputs']['external_imports'], external)

    def test_source_mutation_during_query_is_rejected(self):
        def mutate(root, names):
            (root/'A.lean').write_text('import B\n-- changed\n', encoding='utf-8')
            return self.rows
        with self.assertRaisesRegex(ValueError, 'changed during'):
            self.collect(query=mutate)

    def test_truncated_query_duplicate_import_and_ambiguous_owner_fail(self):
        with self.assertRaisesRegex(ValueError, 'exact requested'):
            self.collect(query=lambda root, names: {'A': self.rows['A']})
        self.rows['A']['imports'] = ['B', 'B']
        with self.assertRaisesRegex(ValueError, 'Malformed compiler'):
            self.collect()
        with self.assertRaisesRegex(ValueError, 'multiple'):
            inventory.collect(self.root, self.paths, {}, {'A': self.builtins['Init']}, query=lambda *_: self.rows)


if __name__ == '__main__':
    unittest.main()
