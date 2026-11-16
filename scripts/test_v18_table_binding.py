"""Reject table incorporation drift and the input-offset error alleged in F120-5."""
from pathlib import Path
import tempfile
import unittest
from check_v18_table_binding import ROOT, input_identity, validate


class TableBindingTests(unittest.TestCase):
    def component(self, family):
        return (ROOT/f'research/version18/{family}/tex/q{family}-rows.tex').read_text(encoding='utf-8')

    def test_current_manuscript(self):
        self.assertEqual(validate()['complete_component_matches'], 2)

    def test_corrupted_fourth_power_is_rejected(self):
        for family in (198, 196):
            with self.subTest(family=family):
                text = self.component(family)
                self.assertIn('225450225', text)
                text = text.replace('225450225', '225450226', 1)
                with self.assertRaisesRegex(ValueError, 'fourth power'):
                    input_identity(text, family)

    def test_missing_correcting_term_is_rejected(self):
        for family in (198, 196):
            with self.subTest(family=family):
                text = self.component(family)
                self.assertIn('- 12Y_{28}Y_{61}', text)
                text = text.replace('- 12Y_{28}Y_{61}', '- 11Y_{28}Y_{61}', 1)
                with self.assertRaisesRegex(ValueError, 'fourth power'):
                    input_identity(text, family)

    def test_manuscript_drift_or_duplicate_component_is_rejected(self):
        for duplicate in (False, True):
            with self.subTest(duplicate=duplicate), tempfile.TemporaryDirectory() as tmp:
                root = Path(tmp)
                pieces = []
                for family in (198, 196):
                    text = self.component(family)
                    path = root/f'research/version18/{family}/tex/q{family}-rows.tex'
                    path.parent.mkdir(parents=True)
                    path.write_text(text, encoding='utf-8')
                    pieces.append(text)
                source = '\n'.join(pieces)
                source = source+pieces[0] if duplicate else source.replace('225450225', '225450226', 1)
                (root/'manuscripts').mkdir()
                (root/'manuscripts/quartic_v18.tex').write_text(source, encoding='utf-8')
                with self.assertRaisesRegex(ValueError, 'exactly once'):
                    validate(root)


if __name__ == '__main__':
    unittest.main()
