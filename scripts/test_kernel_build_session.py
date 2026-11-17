import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import kernel_build_session as session


class SessionTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)/'project'
        self.root.mkdir()
        self.destination = self.root.parent/'stage'
        self.context = {'schema': 'kernel-build-context/v1',
            'environment': {'scope': 'synthetic unit fixture, not a real build'},
            'modules': {'A': {'inputs': {'source_path': 'A.lean', 'source_sha256': 'a'*64,
                'project_imports': [], 'header': {'isModule': False, 'imports': []}}}},
            'project_paths': {'A': {'source_path': 'A.lean',
                'lean_output_prefix': '.lake/build/lib/lean/A', 'ir_output_prefix': '.lake/build/ir/A'}}}
        for path in ['.lake/build/lib/lean/A.'+x for x in ('olean', 'ilean', 'trace')] + [
                '.lake/build/ir/A.c', '.lake/build/ir/A.setup.json']:
            file = self.root/path
            file.parent.mkdir(parents=True, exist_ok=True)
            file.write_bytes(('synthetic unit fixture '+path).encode())
        self.producer = {'repository': 'owner/repo', 'head_sha': 'a'*40, 'run_id': 123,
            'run_attempt': 1, 'workflow_sha256': 'b'*64, 'event': 'push', 'ref': 'refs/heads/main'}
        identity = {'head_sha': 'a'*40, 'contract_sha256': 'c'*64,
            'compiler': 'synthetic unit compiler', 'modules': ['A']}
        self.marker = {'schema': 'kernel-build-complete/v1', 'status': 'complete', 'identity': identity}
        self.audit = {'schema': 'kernel-audit/v1', 'status': 'passed', **identity}

    def built(self):
        return session.record_build(self.root, session.begin(self.context), self.context, self.marker)

    def finish(self, built, **changes):
        args = dict(workspace=self.root, destination=self.destination, session=built,
            context=self.context, build_marker=self.marker, audit_report=self.audit, producer=self.producer)
        args.update(changes)
        return session.finish(**args)

    def test_stable_complete_build_and_full_audit_stage_exact_outputs(self):
        result = self.finish(self.built())
        manifest = json.loads((self.destination/'manifest.json').read_text())
        self.assertEqual(result['phase'], 'staged')
        self.assertEqual(result['staged']['files'], 5)
        self.assertEqual(set(manifest['modules']), {'A'})
        self.assertEqual(manifest['environment'], self.context['environment'])

    def test_recording_owns_its_snapshots(self):
        prepared = session.begin(self.context)
        built = self.built()
        self.context['environment']['changed'] = True
        self.marker['identity']['head_sha'] = 'f'*40
        self.assertNotIn('changed', prepared['context']['environment'])
        self.assertNotIn('changed', built['context']['environment'])
        self.assertEqual(built['build_marker']['identity']['head_sha'], 'a'*40)

    def test_changed_inputs_during_build_or_audit_cannot_stage(self):
        prepared, built = session.begin(self.context), self.built()
        for field in ('environment', 'modules', 'project_paths'):
            changed = copy.deepcopy(self.context)
            if field == 'modules':
                changed[field]['A']['inputs']['source_sha256'] = 'd'*64
            elif field == 'project_paths':
                changed[field]['A']['lean_output_prefix'] = '.lake/build/lib/lean/Elsewhere'
            else:
                changed[field]['runtime'] = 'changed'
            with self.subTest(field=field):
                with self.assertRaisesRegex(ValueError, 'Inputs changed during the build'):
                    session.record_build(self.root, prepared, changed, self.marker)
                with self.assertRaisesRegex(ValueError, 'Inputs changed during the full audit'):
                    self.finish(built, context=changed)
        self.assertFalse(self.destination.exists())

    def test_missing_build_marker_or_wrong_phase_does_not_read_outputs(self):
        with patch.object(session, 'snapshot_outputs') as snapshot:
            for marker in (None, {**self.marker, 'status': 'running'},
                    {**self.marker, 'identity': {**self.marker['identity'], 'modules': []}}):
                with self.assertRaisesRegex(ValueError, 'completed build'):
                    session.record_build(self.root, session.begin(self.context), self.context, marker)
            with self.assertRaisesRegex(ValueError, 'completed build session'):
                self.finish(session.begin(self.context))
            snapshot.assert_not_called()

    def test_audit_failure_wrong_head_or_changed_marker_prevents_publication(self):
        built = self.built()
        for audit in ({**self.audit, 'status': 'failed'}, {**self.audit, 'head_sha': 'e'*40},
                {**self.audit, 'modules': []}):
            with self.assertRaisesRegex(ValueError, 'full audit'):
                self.finish(built, audit_report=audit)
        with self.assertRaisesRegex(ValueError, 'Build marker changed'):
            self.finish(built, build_marker={**self.marker, 'other': 'mutation'})
        self.assertFalse(self.destination.exists())

    def test_output_mutation_during_audit_prevents_publication(self):
        built = self.built()
        (self.root/'.lake/build/lib/lean/A.olean').write_bytes(b'changed during audit')
        with self.assertRaisesRegex(ValueError, 'changed across the audit'):
            self.finish(built)
        self.assertFalse(self.destination.exists())


if __name__ == '__main__':
    unittest.main()
