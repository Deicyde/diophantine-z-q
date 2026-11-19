from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import validate_kernel_reuse_linux as validation


class LiveValidationGuards(unittest.TestCase):
    def test_all_fixture_labels_are_valid_diagnostic_phase_names(self):
        with tempfile.TemporaryDirectory() as directory:
            for case in validation.CASES:
                for phase in ('build', 'audit', 'no-build', 'independent-no-build', 'changed-needs-build'):
                    with self.subTest(case=case, phase=phase):
                        validation.AuditDiagnostics(0, Path(directory), name=case+'-'+phase)

    def test_non_linux_is_rejected_before_creating_an_output(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)/'output'
            with patch.object(validation.sys, 'platform', 'win32'):
                with self.assertRaisesRegex(ValueError, 'must run on Linux'):
                    validation.validate(output, Path(directory))
            self.assertFalse(output.exists())

    def test_credentials_are_rejected_before_creating_an_output(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)/'output'
            with patch.object(validation.sys, 'platform', 'linux'), \
                    patch.dict(validation.os.environ, {'GH_TOKEN': 'unit-fixture'}):
                with self.assertRaisesRegex(ValueError, 'No credentials'):
                    validation.validate(output, Path(directory))
            self.assertFalse(output.exists())

    def test_existing_evidence_is_not_reused_or_overwritten(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)/'output'
            output.mkdir()
            (output/'keep').write_text('prior evidence')
            with patch.object(validation.sys, 'platform', 'linux'), \
                    patch.dict(validation.os.environ, {}, clear=True):
                with self.assertRaisesRegex(ValueError, 'fresh owned output'):
                    validation.validate(output, Path(directory))
            self.assertEqual((output/'keep').read_text(), 'prior evidence')


if __name__ == '__main__':
    unittest.main()
