"""Authenticated producer selection tests; no network calls or candidate code."""
import base64
import copy
import hashlib
import unittest

import kernel_build_source as source
from kernel_build_manifest import WORKFLOW, JOB


class SelectionTests(unittest.TestCase):
    def setUp(self):
        self.prefix = '/repos/owner/repo'
        self.commit, self.main = 'a' * 40, 'b' * 40
        workflow = b'reviewed cold producer workflow'
        self.workflow_hash = hashlib.sha256(workflow).hexdigest()
        self.run = {'id': 12, 'run_attempt': 2, 'repository': {'full_name': 'owner/repo'},
                    'head_repository': {'full_name': 'owner/repo'}, 'head_sha': self.commit,
                    'head_branch': 'main', 'event': 'workflow_dispatch', 'path': WORKFLOW,
                    'status': 'completed', 'conclusion': 'success'}
        self.job = {'id': 90, 'run_id': 12, 'run_attempt': 2, 'head_sha': self.commit,
                    'name': JOB, 'status': 'completed', 'conclusion': 'success'}
        self.artifact = {'id': 91, 'expired': False, 'name': 'kernel-main-build-12-2',
                         'digest': 'sha256:' + 'c' * 64,
                         'workflow_run': {'id': 12, 'head_sha': self.commit}}
        self.routes = {
            '': {'full_name': 'owner/repo', 'default_branch': 'main'},
            '/git/ref/heads/main': {'ref': 'refs/heads/main',
                                   'object': {'type': 'commit', 'sha': self.main}},
            '/actions/workflows/kernel-lean.yml/runs?branch=main&status=success&per_page=100':
                {'workflow_runs': [{'id': 12}]},
            '/actions/runs/12': self.run,
            f'/compare/{self.commit}...{self.main}': {
                'base_commit': {'sha': self.commit}, 'merge_base_commit': {'sha': self.commit},
                'behind_by': 0, 'status': 'ahead'},
            f'/contents/{WORKFLOW}?ref={self.commit}': {
                'path': WORKFLOW, 'type': 'file', 'encoding': 'base64', 'size': len(workflow),
                'content': base64.b64encode(workflow).decode()},
            '/actions/runs/12/attempts/2/jobs?per_page=100&page=1':
                {'total_count': 1, 'jobs': [self.job]},
            '/actions/runs/12/artifacts?per_page=100&page=1':
                {'total_count': 1, 'artifacts': [self.artifact]},
            '/actions/artifacts/91': self.artifact,
        }
        self.calls = []

    def api(self, path):
        self.calls.append(path)
        self.assertTrue(path.startswith(self.prefix))
        value = self.routes[path[len(self.prefix):]]
        return copy.deepcopy(value() if callable(value) else value)

    def select(self):
        return source.select_producer(self.api, 'owner/repo', self.workflow_hash)

    def test_successful_main_dispatch_binds_all_receipts(self):
        result = self.select()
        self.assertEqual(result['status'], 'selected')
        self.assertEqual(result['observed_main'], self.main)
        self.assertEqual(result['producer']['run_attempt'], 2)
        self.assertEqual(result['producer']['head_sha'], self.commit)
        self.assertEqual(result['producer']['event'], 'workflow_dispatch')
        self.assertEqual(result['job_id'], 90)
        self.assertEqual(result['artifact_id'], 91)
        self.assertEqual(result['archive_sha256'], 'c' * 64)

    def test_branch_fork_failed_and_running_producers_are_never_selected(self):
        good = copy.deepcopy(self.run)
        for key, value in [('head_branch', 'reserved/familiar-name'), ('event', 'pull_request'),
                           ('head_repository', {'full_name': 'fork/repo'}),
                           ('repository', None), ('conclusion', 'failure'),
                           ('status', 'in_progress')]:
            self.run.clear()
            self.run.update(good)
            self.run[key] = value
            self.calls.clear()
            with self.subTest(key=key):
                self.assertEqual(self.select()['status'], 'cold')
                self.assertFalse(any('/artifacts' in path for path in self.calls))

    def test_compare_must_prove_ancestry_not_merely_a_familiar_main_label(self):
        key = f'/compare/{self.commit}...{self.main}'
        good = copy.deepcopy(self.routes[key])
        for field, value in [('behind_by', 1), ('behind_by', False), ('status', 'diverged'),
                             ('merge_base_commit', {'sha': 'd' * 40}),
                             ('base_commit', {'sha': 'd' * 40})]:
            self.routes[key] = {**good, field: value}
            with self.subTest(field=field):
                self.assertEqual(self.select()['status'], 'cold')

    def test_workflow_mismatch_is_cold_without_an_artifact_read(self):
        self.workflow_hash = 'd' * 64
        self.assertEqual(self.select()['status'], 'cold')
        self.assertFalse(any('/artifacts' in path for path in self.calls))

    def test_later_pages_are_read_and_duplicate_kernel_jobs_are_refused(self):
        jobs = [{'id': 1000+i, 'name': 'unrelated'} for i in range(100)]
        first = '/actions/runs/12/attempts/2/jobs?per_page=100&page=1'
        second = '/actions/runs/12/attempts/2/jobs?per_page=100&page=2'
        self.routes[first] = {'total_count': 101, 'jobs': jobs}
        self.routes[second] = {'total_count': 101, 'jobs': [self.job]}
        self.assertEqual(self.select()['status'], 'selected')
        jobs[0]['name'] = JOB
        self.assertEqual(self.select()['status'], 'cold')

    def test_later_artifact_page_is_read_and_changed_count_is_refused(self):
        first = '/actions/runs/12/artifacts?per_page=100&page=1'
        second = '/actions/runs/12/artifacts?per_page=100&page=2'
        self.routes[first] = {'total_count': 101, 'artifacts': [
            {'id': 1000+i, 'name': 'unrelated'} for i in range(100)]}
        self.routes[second] = {'total_count': 101, 'artifacts': [self.artifact]}
        self.assertEqual(self.select()['status'], 'selected')
        self.routes[second]['total_count'] = 102
        self.assertEqual(self.select()['status'], 'cold')

    def test_truncated_or_duplicate_page_is_cold(self):
        path = '/actions/runs/12/artifacts?per_page=100&page=1'
        for response in ({'total_count': 2, 'artifacts': [self.artifact]},
                         {'total_count': 2, 'artifacts': [self.artifact, self.artifact]},
                         {'total_count': True, 'artifacts': [self.artifact]}):
            self.routes[path] = response
            with self.subTest(response=response):
                self.assertEqual(self.select()['status'], 'cold')

    def test_fresh_run_recheck_catches_retry_started_during_selection(self):
        reads = 0

        def changing():
            nonlocal reads
            reads += 1
            return self.run if reads == 1 else {**self.run, 'run_attempt': 3, 'status': 'queued'}

        self.routes['/actions/runs/12'] = changing
        self.assertEqual(self.select()['status'], 'cold')

    def test_fresh_artifact_not_candidate_claim_must_bind_exact_attempt_and_digest(self):
        for field, value in [('expired', True), ('name', 'kernel-main-build-12-1'),
                             ('id', 92), ('digest', None), ('workflow_run', {'id': 13})]:
            self.routes['/actions/artifacts/91'] = {**self.artifact, field: value}
            with self.subTest(field=field):
                self.assertEqual(self.select()['status'], 'cold')

    def test_bad_configuration_or_main_identity_stops_before_candidate_lookup(self):
        for repository in ('../owner/repo', 'https://foreign.example/repo', 'owner/repo?token=x'):
            with self.subTest(repository=repository), self.assertRaises(ValueError):
                source.select_producer(self.api, repository, self.workflow_hash)
        self.routes['']['default_branch'] = 'other'
        with self.assertRaises(ValueError):
            self.select()

    def test_no_artifact_is_an_explicit_cold_build(self):
        self.routes['/actions/runs/12/artifacts?per_page=100&page=1'] = {
            'total_count': 0, 'artifacts': []}
        result = self.select()
        self.assertEqual(result['status'], 'cold')
        self.assertEqual(result['rejected'], [{'run_id': 12,
                                              'reason': 'Missing or ambiguous main-build artifact'}])


if __name__ == '__main__':
    unittest.main()
