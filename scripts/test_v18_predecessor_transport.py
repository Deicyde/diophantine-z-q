"""Regression tests for the printed214 -> 212 -> 204 finite certificate."""
from pathlib import Path
import tempfile
import unittest

import check_v18_predecessor_transport as check

ROOT = Path(__file__).resolve().parents[1]


class PredecessorTransportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = (ROOT / 'manuscripts/quartic_v18.tex').read_text(encoding='utf-8')

    def changed_source(self, old, new):
        # Only change the table, not an earlier occurrence of its notation.
        start = self.source.index(r'\label{q214:rows}')
        before, table = self.source[:start], self.source[start:]
        self.assertIn(old, table)
        return before + table.replace(old, new, 1)

    def reject(self, source, message):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'changed.tex'
            path.write_text(source, encoding='utf-8')
            with self.assertRaisesRegex(ValueError, message):
                check.check(ROOT, manuscript=path)

    def test_complete_printed_source_and_transport(self):
        result = check.check(ROOT)
        self.assertEqual(result['printed214_rows'], 188)
        self.assertEqual(len(result['additive212_rows']), 186)
        self.assertEqual(len(result['reciprocal204_rows']), 186)
        self.assertEqual(len(result['reciprocal204_formal_ids']), 204)

    def test_changed_small_coefficient_is_rejected(self):
        self.reject(self.changed_source(r'9792\,X_{109}', r'9793\,X_{109}'),
                    'Printed214 row mismatch 51')

    def test_changed_decimal_chunk_is_rejected(self):
        self.reject(self.changed_source(r'98194\cdot10^{100}', r'98195\cdot10^{100}'),
                    'Printed214 row mismatch 50')

    def test_unknown_expression_in_decimal_chunk_is_rejected(self):
        self.reject(self.changed_source(r'98194\cdot10^{100}', r'98194\cdot11^{100}'),
                    'Unsupported printed decimal chunk')

    def test_missing_printed_row_is_rejected(self):
        self.reject(self.changed_source(r'\paragraph{Row 51.}', r'\paragraph{Omitted row.}'),
                    'Printed214 residual coverage')

    def test_mismatched_row_number_is_rejected(self):
        self.reject(self.changed_source(r'r_{51,N}', r'r_{52,N}'), 'Printed row label mismatch')

    def test_coordinate_renaming_is_rejected(self):
        # The coordinate dictionary is part of the certificate, not just the
        # numbered equations: an unchanged polynomial in relabelled physical
        # coordinates must not pass.
        import re
        match = re.search(r'1 & \\nolinkurl\{([^}]+)\} & (\d+)\\\\',
                          self.source[self.source.index(r'\label{q214:rows}'):])
        self.assertIsNotNone(match)
        self.reject(self.changed_source(match[0], match[0].replace(match[1], 'incorrect-coordinate')),
                    'Printed214 coordinate mismatch')


if __name__ == '__main__':
    unittest.main()
