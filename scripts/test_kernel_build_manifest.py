"""No network, secrets, Lean execution or repository mutation in these tests."""
import copy
import hashlib
import io
import json
import stat
import unittest
import zipfile

import kernel_build_manifest as kb


def source(name, dependencies=()):
    return {'inputs': {'source_path': name + '.lean',
            'source_sha256': hashlib.sha256(name.encode()).hexdigest(),
            'header': {'isModule': False, 'imports': [
                {'module': dep, 'isMeta': False, 'isExported': True, 'importAll': False}
                for dep in dependencies]},
            'project_imports': list(dependencies)}}


class ManifestTests(unittest.TestCase):
    def setUp(self):
        self.run = {'id': 12, 'run_attempt': 2, 'repository': {'full_name': 'owner/repo'},
                    'head_repository': {'full_name': 'owner/repo'}, 'head_sha': 'a' * 40,
                    'head_branch': 'main', 'event': 'push', 'path': kb.WORKFLOW,
                    'status': 'completed', 'conclusion': 'success'}
        self.job = {'id': 90, 'run_id': 12, 'run_attempt': 2, 'head_sha': 'a' * 40,
                    'name': kb.JOB, 'status': 'completed', 'conclusion': 'success'}
        self.artifact = {'id': 91, 'expired': False, 'name': 'kernel-main-build-12-2',
                         'digest': 'sha256:' + 'c' * 64,
                         'workflow_run': {'id': 12, 'head_sha': 'a' * 40}}
        self.args = dict(repository='owner/repo', approved_workflow_sha256='b' * 64,
                         observed_workflow_sha256='b' * 64, main_commit='a' * 40,
                         archive_sha256='c' * 64)
        self.producer = kb.authenticated_producer(self.run, self.job, self.artifact, **self.args)
        self.outputs = {'.lake/build/lib/lean/A.olean': b'real output bytes are hashed',
                        '.lake/build/lib/lean/A.trace': b'no trust from a source hash alone',
                        'lean/.lake/build/lib/lean/B.olean': b'local package',
                        'lean/.lake/build/lib/lean/B.trace': b'local trace'}
        self.manifest = {'schema': kb.SCHEMA, 'producer': self.producer,
                         'environment': {'compiler': 'pinned', 'packages': 'pinned'},
                         'modules': {'A': source('A', ['B']), 'B': source('B')},
                         'outputs': {p: {'size': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
                                     for p, data in self.outputs.items()}}
        self.manifest['modules']['B']['inputs']['source_path'] = 'lean/B.lean'
        for name, entry in self.manifest['modules'].items():
            entry['outputs'] = [p for p in self.outputs if '/' + name + '.' in p]

    def archive(self, manifest=None, outputs=None, extras=()):
        stream = io.BytesIO()
        with zipfile.ZipFile(stream, 'w') as z:
            z.writestr('manifest.json', json.dumps(manifest or self.manifest))
            for name, data in (self.outputs if outputs is None else outputs).items():
                z.writestr('outputs/' + name, data)
            for name, data in extras:
                z.writestr(name, data)
        return stream

    def verify(self, stream):
        return kb.verify_archive(stream, hashlib.sha256(stream.getvalue()).hexdigest(), self.producer)

    def test_both_root_and_local_package_outputs_are_verified(self):
        self.assertEqual(self.verify(self.archive()), self.manifest)

    def test_main_push_and_exact_attempt_job_success_are_mandatory(self):
        for key, value in [('event', 'pull_request'), ('event', 'workflow_dispatch'),
                           ('head_branch', 'codex/protocol-b-kernel/12/reserved'),
                           ('head_branch', 'Main'), ('head_sha', 'f' * 40),
                           ('conclusion', 'failure'), ('status', 'in_progress'),
                           ('path', '.github/workflows/other.yml'), ('run_attempt', True),
                           ('repository', {'full_name': 'fork/repo'}),
                           ('repository', ['not', 'an', 'object']),
                           ('head_repository', {'full_name': 'fork/repo'})]:
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                kb.authenticated_producer({**self.run, key: value}, self.job, self.artifact, **self.args)
        for key, value in [('run_attempt', 1), ('run_id', 11), ('id', True),
                           ('status', 'in_progress'), ('conclusion', 'cancelled'),
                           ('name', 'lookalike job'), ('head_sha', 'd' * 40)]:
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                kb.authenticated_producer(self.run, {**self.job, key: value}, self.artifact, **self.args)

    def test_workflow_pin_and_immutable_artifact_binding_are_mandatory(self):
        for key, value in [('expired', True), ('id', True), ('name', 'kernel-main-build-12-1'),
                           ('digest', 'sha256:' + 'd' * 64),
                           ('workflow_run', {'id': 12, 'head_sha': 'd' * 40}),
                           ('workflow_run', {'id': 13, 'head_sha': 'a' * 40})]:
            with self.subTest(key=key), self.assertRaises(ValueError):
                kb.authenticated_producer(self.run, self.job, {**self.artifact, key: value}, **self.args)
        with self.assertRaises(ValueError):
            kb.authenticated_producer(self.run, self.job, self.artifact,
                                      **{**self.args, 'observed_workflow_sha256': 'e' * 64})

    def test_poisoned_olean_and_trace_fail_even_when_source_hash_is_unchanged(self):
        for path in self.outputs:
            bad = dict(self.outputs)
            bad[path] += b'poison'
            with self.subTest(path=path), self.assertRaisesRegex(ValueError, 'size mismatch'):
                self.verify(self.archive(outputs=bad))
            bad[path] = b'x' * len(self.outputs[path])
            with self.subTest(path=path), self.assertRaisesRegex(ValueError, 'hash mismatch'):
                self.verify(self.archive(outputs=bad))
        with self.assertRaisesRegex(ValueError, 'artifact digest'):
            kb.verify_archive(self.archive(), '0' * 64, self.producer)

    def test_missing_extra_traversal_and_symlink_members_fail_before_restore(self):
        with self.assertRaisesRegex(ValueError, 'inventories differ'):
            self.verify(self.archive(outputs=dict(list(self.outputs.items())[:-1])))
        for name in ('outputs/.lake/build/../outside', '/absolute', 'outputs/lean/.lake/build/A:ads',
                     'outputs/.lake/build/A\\B', 'unexpected'):
            with self.subTest(name=name), self.assertRaises(ValueError):
                self.verify(self.archive(extras=[(name, b'evil')]))
        link = zipfile.ZipInfo('outputs/.lake/build/symlink')
        link.create_system = 3
        link.external_attr = (stat.S_IFLNK | 0o777) << 16
        with self.assertRaisesRegex(ValueError, 'non-file'):
            self.verify(self.archive(extras=[(link, b'/outside')]))
        with self.assertRaises(ValueError):
            self.verify(self.archive(extras=[('outputs/.lake/build/extra', b'extra')]))

    def test_unowned_multiply_owned_and_wrong_producer_manifest_fail(self):
        bad = copy.deepcopy(self.manifest)
        bad['producer']['run_attempt'] = 1
        with self.assertRaisesRegex(ValueError, 'producer'):
            self.verify(self.archive(manifest=bad))
        bad = copy.deepcopy(self.manifest)
        bad['modules']['A']['outputs'].append(bad['modules']['B']['outputs'][0])
        with self.assertRaisesRegex(ValueError, 'belong|multiply owned'):
            self.verify(self.archive(manifest=bad))
        bad = copy.deepcopy(self.manifest)
        bad['modules']['A']['outputs'].remove('.lake/build/lib/lean/A.trace')
        with self.assertRaisesRegex(ValueError, 'Incomplete Lean'):
            self.verify(self.archive(manifest=bad))

    def test_duplicate_json_keys_and_nonfinite_values_are_refused(self):
        for raw in ('{"a":1,"a":2}', '{"a":NaN}', '{"a":Infinity}'):
            with self.subTest(raw=raw), self.assertRaises(ValueError):
                kb.unique_json(raw)

    def test_changed_closure_environment_and_module_removal(self):
        old = {'A': source('A'), 'B': source('B', ['A']), 'C': source('C', ['B']), 'D': source('D')}
        new = copy.deepcopy(old)
        env = {'compiler': 'pinned'}
        self.assertEqual(kb.reusable_modules(old, new, env, env), set(old))
        new['B']['inputs']['source_sha256'] = 'f' * 64
        self.assertEqual(kb.reusable_modules(old, new, env, env), {'A', 'D'})
        self.assertEqual(kb.reusable_modules(old, new, env, {'compiler': 'changed'}), set())
        del new['A']
        with self.assertRaisesRegex(ValueError, 'import inventory'):
            kb.reusable_modules(old, new, env, env)

    def test_deep_graph_does_not_hit_python_recursion_limit_and_cycles_fail(self):
        nodes = {str(i): source(str(i), [str(i-1)] if i else []) for i in range(4000)}
        env = {'compiler': 'pinned'}
        self.assertEqual(len(kb.reusable_modules(nodes, nodes, env, env)), 4000)
        nodes['0']['inputs']['project_imports'] = ['3999']
        nodes['0']['inputs']['header'] = source('0', ['3999'])['inputs']['header']
        with self.assertRaisesRegex(ValueError, 'Cyclic'):
            kb.reusable_modules(nodes, nodes, env, env)


if __name__ == '__main__':
    unittest.main()
