import copy
import unittest
from kernel_build_changes import InputContextMismatch


class ChangeDiagnosticsTests(unittest.TestCase):
    def test_changed_bytes_modes_added_and_removed_files_are_distinguished(self):
        before = {'a': {'sha256': 'a'*64, 'mode': 420},
                  'b': {'sha256': 'b'*64, 'mode': 420},
                  'removed': {'sha256': 'c'*64}}
        after = copy.deepcopy(before)
        after['a']['sha256'] = 'd'*64
        after['b']['mode'] = 292
        del after['removed']
        after['added'] = {'sha256': 'e'*64}
        error = InputContextMismatch('refused', {'dependency_inputs': 'old'},
            {'dependency_inputs': 'new'}, {'dependency_files': {'dep': after}})
        report = error.report({'installed_inputs': {'dependency_files': {'dep': before}}})
        self.assertEqual(report['changed_file_counts'], {'dependency/dep': 4})
        self.assertEqual({r['path'] for r in report['file_examples']}, set(before)|set(after))
        self.assertEqual(report['decision'], 'rejected')
        self.assertFalse(report['acceptance'])
        self.assertFalse(report['file_examples_truncated'])

    def test_bounded_examples_still_count_every_changed_file(self):
        files = {str(i): {'sha256': 'a'*64} for i in range(350)}
        error = InputContextMismatch('refused', {'toolchain': 'old'},
            {'toolchain': 'new'}, {'toolchain_files': files})
        report = error.report({'installed_inputs': {'toolchain_files': {}}})
        self.assertEqual(report['changed_file_counts'], {'toolchain': 350})
        self.assertEqual(len(report['file_examples']), 100)
        self.assertTrue(report['file_examples_truncated'])

    def test_environment_values_are_not_copied_to_diagnostic(self):
        error = InputContextMismatch('refused', {'environment_overrides': {'CC': 'old-private-path'}},
            {'environment_overrides': {'CC': 'new-private-path'}}, {})
        self.assertNotIn('private-path', str(error))
        self.assertNotIn('private-path', str(error.report()))
        self.assertEqual(error.report()['changed_categories'], ['environment_overrides'])
        self.assertFalse(error.report()['previous_file_inventory_available'])


if __name__ == '__main__':
    unittest.main()
