import copy
import hashlib
import io
import json
from pathlib import Path
import tempfile
import unittest
import zipfile

import kernel_build_producer as producer
from kernel_build_manifest import verify_archive


class ProducerTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)/'project'
        self.root.mkdir()
        self.modules, self.paths = {}, {}
        for name, prefix in (('A', ''), ('B', 'lean/')):
            self.modules[name] = {'inputs': {'source_path': prefix+name+'.lean',
                'source_sha256': 'a'*64, 'project_imports': [],
                'header': {'isModule': False, 'imports': []}}}
            lean = prefix+'.lake/build/lib/lean/'+name
            ir = prefix+'.lake/build/ir/'+name
            self.paths[name] = {'source_path': prefix+name+'.lean',
                'lean_output_prefix': lean, 'ir_output_prefix': ir}
            for path in [lean+'.'+x for x in ('olean', 'ilean', 'trace', 'olean.hash')] + [ir+'.c', ir+'.setup.json']:
                file = self.root/path
                file.parent.mkdir(parents=True, exist_ok=True)
                file.write_bytes(('synthetic unit fixture '+path).encode())
        self.environment = {'scope': 'synthetic unit fixture, not a real build'}
        self.context = {'repository': 'owner/repo', 'head_sha': 'a'*40, 'run_id': 123,
                        'run_attempt': 1, 'workflow_sha256': 'b'*64,
                        'event': 'push', 'ref': 'refs/heads/main'}
        self.identity = {'head_sha': 'a'*40, 'contract_sha256': 'c'*64,
                         'compiler': 'synthetic unit compiler', 'modules': ['A', 'B']}
        self.marker = {'schema': 'kernel-build-complete/v1', 'status': 'complete',
                       'identity': self.identity}
        self.audit = {'schema': 'kernel-audit/v1', 'status': 'passed', **self.identity}

    def snapshot(self):
        return producer.snapshot_outputs(self.root, self.modules, self.paths)

    def manifest(self, before=None, after=None, **replace):
        snapshot = self.snapshot() if before is None else before
        args = {'before': snapshot, 'after': snapshot if after is None else after,
            'environment_before': self.environment, 'environment_after': self.environment,
            'build_marker': self.marker, 'audit_report': self.audit, 'producer': self.context}
        args.update(replace)
        return producer.make_manifest(**args)

    def test_both_output_roots_form_a_consumer_verifiable_staged_artifact(self):
        manifest = self.manifest()
        stage = self.root.parent/'stage'
        result = producer.stage_outputs(self.root, stage, manifest)
        self.assertEqual(result['files'], 12)
        stream = io.BytesIO()
        with zipfile.ZipFile(stream, 'w') as archive:
            for file in stage.rglob('*'):
                if file.is_file(): archive.write(file, file.relative_to(stage).as_posix())
        digest = hashlib.sha256(stream.getvalue()).hexdigest()
        self.assertEqual(verify_archive(stream, digest, self.context), manifest)
        self.assertEqual(json.loads((stage/'manifest.json').read_text()), manifest)

    def test_missing_outputs_and_unknown_extensions_do_not_publish(self):
        target = self.root/(self.paths['A']['lean_output_prefix']+'.ilean')
        target.unlink()
        with self.assertRaisesRegex(ValueError, 'Missing required'):
            self.snapshot()
        target.write_bytes(b'unit fixture')
        unknown = self.root/(self.paths['A']['lean_output_prefix']+'.unrecognized.py')
        unknown.write_bytes(b'not an allowed build output')
        with self.assertRaisesRegex(ValueError, 'Unknown module output'):
            self.snapshot()

    def test_module_system_outputs_are_required_when_used(self):
        self.modules['A']['inputs']['header']['isModule'] = True
        with self.assertRaisesRegex(ValueError, 'Missing required'):
            self.snapshot()
        for suffix in ('olean.server', 'olean.private', 'ir', 'ir.sig'):
            (self.root/(self.paths['A']['lean_output_prefix']+'.'+suffix)).write_bytes(b'unit fixture')
        self.assertEqual(len(self.snapshot()['outputs']), 16)

    def test_any_source_or_output_change_across_audit_blocks_publication(self):
        before = self.snapshot()
        for what in ('outputs', 'source'):
            with self.subTest(what=what):
                after = copy.deepcopy(before)
                if what == 'source':
                    after['modules']['A']['inputs']['source_sha256'] = 'f'*64
                else:
                    next(iter(after['outputs'].values()))['sha256'] = 'f'*64
                with self.assertRaisesRegex(ValueError, 'changed across'):
                    self.manifest(before, after)
        with self.assertRaisesRegex(ValueError, 'environment changed'):
            self.manifest(environment_after={'different': True})

    def test_incomplete_wrong_head_or_wrong_scope_audit_cannot_authorize_outputs(self):
        for key, value in (('status', 'failed'), ('head_sha', 'd'*40),
                           ('contract_sha256', 'd'*64), ('compiler', 'other'), ('modules', ['A'])):
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'full audit'):
                self.manifest(audit_report={**self.audit, key: value})
        with self.assertRaisesRegex(ValueError, 'completed build'):
            self.manifest(build_marker={**self.marker, 'status': 'partial'})

    def test_producer_must_be_exact_main_with_run_and_attempt_identity(self):
        for key, value in (('ref', 'refs/heads/Main'), ('ref', 'refs/pull/12/merge'),
                           ('event', 'pull_request'), ('run_id', True), ('run_attempt', 0),
                           ('workflow_sha256', 'not-a-digest')):
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, 'producer context'):
                self.manifest(producer={**self.context, key: value})

    def test_changed_file_during_staging_leaves_no_manifest(self):
        manifest = self.manifest()
        relative = next(iter(manifest['outputs']))
        (self.root/relative).write_bytes(b'changed after the audit')
        destination = self.root.parent/'failed-stage'
        with self.assertRaisesRegex(ValueError, 'changed after|grew during'):
            producer.stage_outputs(self.root, destination, manifest)
        self.assertFalse((destination/'manifest.json').exists())

    def test_existing_stage_is_not_overwritten(self):
        destination = self.root.parent/'stage'
        destination.mkdir()
        (destination/'keep').write_text('existing evidence')
        with self.assertRaisesRegex(ValueError, 'not new'):
            producer.stage_outputs(self.root, destination, self.manifest())
        self.assertEqual((destination/'keep').read_text(), 'existing evidence')


if __name__ == '__main__':
    unittest.main()
