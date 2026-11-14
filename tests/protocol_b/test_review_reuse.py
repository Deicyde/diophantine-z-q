"""Authenticated completed-review reuse; no provider or GitHub requests."""
import copy
import base64
import hashlib
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
import zipfile
from unittest.mock import patch

from test_gate import APP_ID, BASE, HEAD, FakeApp, FakeGH, changed, comment, envelope, gate, report, run_pipeline


def original_input(gh):
    return {'repository': gh.repo, 'pull_request': gh.pr['number'], 'head': gh.pr['head']['sha'],
            'base': gh.pr['base']['sha'], 'change_class': 'local mathematical',
            'untrusted_title': gh.pr['title'], 'untrusted_description': gh.pr['body'],
            'files': [changed('p.tex')]}


class Reuse(unittest.TestCase):
    def fixtures(self):
        gh, app = FakeGH(), FakeApp()
        gh.permission = 'write'
        accepted = envelope(read_prerequisites_complete=True)
        failed = envelope('fable', complete=False, review=report(decision='changes_requested'))
        compact = copy.deepcopy(accepted)
        compact['review'].pop('report')
        compact['review'].pop('sources_read')
        app.prior({'astra': compact, 'fable': failed})
        gh.review_material = lambda row: (copy.deepcopy(accepted), {'discussion': [], 'prior_findings': {}, 'overrides': {}}, original_input(gh), [])
        event = {'issue': {'number': 1}, 'comment': comment('/protocol-b review', 'collaborator'),
                 'sender': {'login': 'collaborator'}}
        return gh, app, accepted, event

    def test_command_reuses_astra_acceptance_and_calls_only_fable(self):
        gh, app, accepted, event = self.fixtures()
        called = []
        def provider(reviewer):
            called.append(reviewer.family)
            return report()
        _, _, errors, state = run_pipeline(gh, app, provider=provider, event=event)
        self.assertEqual(errors, [])
        self.assertEqual(called, ['fable'])
        self.assertEqual(state['reports']['astra'], accepted)
        self.assertEqual(state['conclusion'], 'success')
        self.assertIn('Reused authenticated same-head acceptance', state['summary'])

    def test_invalid_or_forged_acceptance_cannot_be_reused(self):
        cases = ['wrong_app', 'wrong_head', 'wrong_model', 'incomplete', 'missing_reads', 'unresolved']
        for case in cases:
            with self.subTest(case=case):
                gh, app, accepted, event = self.fixtures()
                if case == 'wrong_app':
                    app.checks[5]['app']['id'] = APP_ID + 1
                elif case == 'wrong_head':
                    accepted['head'] = 'c' * 40
                elif case == 'wrong_model':
                    accepted['model'] = 'self-asserted-reviewer'
                elif case == 'incomplete':
                    accepted['complete'] = False
                elif case == 'missing_reads':
                    accepted['read_prerequisites_complete'] = False
                else:
                    accepted['review'] = report(decision='changes_requested')
                if case != 'wrong_app':
                    app.prior({'astra': accepted, 'fable': envelope('fable', complete=False)})
                called = []
                def provider(reviewer):
                    called.append(reviewer.family)
                    return report()
                _, _, errors, state = run_pipeline(gh, app, provider=provider, event=event)
                self.assertEqual(errors, [])
                self.assertCountEqual(called, ['astra', 'fable'])

    def test_new_prior_finding_prevents_reuse(self):
        gh, app, accepted, _ = self.fixtures()
        with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
             patch.dict(os.environ, {'APP_ID': str(APP_ID)}):
            result = gate.reusable_acceptances(gh, app, gh.pr, 'Protocol B / test review', 20,
                                              BASE, {'new-F1': {}}, {}, [], [changed('p.tex')], 'local mathematical')
        self.assertEqual(result, {})

    def test_changed_plain_objection_or_interrupted_note_requires_fresh_review(self):
        for discussion in [
            [{'id': 100, 'author': 'mathematician', 'created': 'later', 'body': 'The new lemma fails at zero.'}],
            [{'incomplete_review': {'reviewer': 'fable', 'notes': ['The endpoint case is missing.']}, 'source': 'https://example.org/comment'}]
        ]:
            with self.subTest(discussion=discussion):
                gh, app, _, _ = self.fixtures()
                with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
                     patch.dict(os.environ, {'APP_ID': str(APP_ID)}):
                    result = gate.reusable_acceptances(gh, app, gh.pr, 'Protocol B / test review', 20,
                                                      BASE, {}, {}, discussion, [changed('p.tex')], 'local mathematical')
                self.assertEqual(result, {})

    def test_only_literal_retry_and_exact_round_pointer_are_non_substantive(self):
        pointer = gate.ROUND_MARKER + '\n```json\n' + json.dumps({'check': 1}) + '\n```'
        self.assertEqual(gate.substantive_history([
            {'body': '/protocol-b review'}, {'author': 'github-actions[bot]', 'body': pointer}]), [])
        for body in ['/protocol-b review\nAlso: the lemma is false.', pointer + '\nAn objection',
                     gate.ROUND_MARKER + '\nnot valid JSON']:
            self.assertEqual(len(gate.substantive_history([{'author': 'github-actions[bot]', 'body': body}])), 1)

    def test_publish_compact_record_then_retrieve_and_retry(self):
        gh, app = FakeGH(), FakeApp()
        def first(reviewer):
            if reviewer.family == 'fable':
                raise RuntimeError('fixture infrastructure failure')
            reviewer.history_read, reviewer.reads = True, [{'path': 'source.tex'}]
            return report()
        _, _, errors, state = run_pipeline(gh, app, provider=first)
        self.assertTrue(errors)
        stored = json.loads(app.checks[20]['output']['text'])['reports']
        self.assertNotIn('report', stored['astra']['review'])
        self.assertNotIn('sources_read', stored['astra']['review'])
        second_gh, second_app = FakeGH(), FakeApp()
        second_gh.permission = 'write'
        second_app.prior(stored)
        second_gh.review_material = lambda row: (copy.deepcopy(state['reports']['astra']),
                                                 {'discussion': [], 'prior_findings': {}, 'overrides': {}}, original_input(second_gh), [])
        event = {'issue': {'number': 1}, 'comment': comment('/protocol-b review', 'collaborator'),
                 'sender': {'login': 'collaborator'}}
        called = []
        def second(reviewer):
            called.append(reviewer.family)
            return report()
        _, _, errors, retried = run_pipeline(second_gh, second_app, provider=second, event=event)
        self.assertEqual(errors, [])
        self.assertEqual(called, ['fable'])
        self.assertEqual(retried['reports']['astra'], state['reports']['astra'])

    def test_artifact_recovery_matches_original_app_record(self):
        full = envelope(read_prerequisites_complete=True)
        compact = copy.deepcopy(full)
        compact['review'].pop('report')
        compact['review'].pop('sources_read')
        context = {'head': HEAD, 'trusted_workflow': BASE, 'discussion': [], 'prior_findings': {}, 'overrides': {}}
        buf = io.BytesIO()
        with zipfile.ZipFile(buf, 'w') as archive:
            archive.writestr('astra-report.json', json.dumps(full))
            archive.writestr('context.json', json.dumps(context))
            archive.writestr('astra-input.json', json.dumps({'input': original_input(FakeGH())}))
            archive.writestr('astra-source-reads.json', '[]')
        gh = gate.GitHub('x/y', 'fake')
        def get(path):
            if path == '/actions/runs/1':
                return {'id': 1, 'path': gate.WORKFLOW, 'event': 'pull_request_target', 'head_sha': HEAD, 'run_attempt': 1}
            if path == '/actions/runs/1/artifacts?per_page=100&page=1':
                return {'artifacts': [{'id': 20, 'name': 'protocol-b-1-1', 'expired': False}]}
            raise AssertionError(path)
        with patch.object(gh, 'call', side_effect=get), patch.object(gate.urllib.request, 'build_opener') as opener:
            opener.return_value.open.return_value = io.BytesIO(buf.getvalue())
            self.assertEqual(gh.review_material(compact), (full, context, original_input(FakeGH()), []))
        altered = copy.deepcopy(compact)
        altered['review']['not_outside_reviewed'] = ['Different scope']
        with patch.object(gh, 'call', side_effect=get), patch.object(gate.urllib.request, 'build_opener') as opener:
            opener.return_value.open.return_value = io.BytesIO(buf.getvalue())
            with self.assertRaisesRegex(ValueError, 'does not match'):
                gh.review_material(altered)

    def test_same_commit_with_different_pr_scope_or_base_source_is_not_reused(self):
        for change in ('number', 'files', 'base_source'):
            with self.subTest(change=change):
                gh, app, accepted, _ = self.fixtures()
                source_input = original_input(gh)
                reads = []
                if change == 'number':
                    source_input['pull_request'] = 99
                elif change == 'files':
                    source_input['files'] = [changed('different.tex')]
                else:
                    reads = [{'path': 'base-policy.md', 'revision': BASE}]
                    gh.pr['base']['sha'] = 'd' * 40
                    gh.text = lambda path, ref: ref if path == 'base-policy.md' else 'same'
                gh.review_material = lambda row: (accepted, {'discussion': [], 'prior_findings': {}, 'overrides': {}}, source_input, reads)
                with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
                     patch.dict(os.environ, {'APP_ID': str(APP_ID)}):
                    result = gate.reusable_acceptances(gh, app, gh.pr, 'Protocol B / test review', 20,
                                                      BASE, {}, {}, [], [changed('p.tex')], 'local mathematical')
                self.assertEqual(result, {})

    def test_transport_migration_requires_exact_pair_and_same_instructions(self):
        old, new = 'old-workflow', 'new-workflow'
        policy = {'schema': 'protocol-b-review-compatibility/v1', 'migrations': [{
            'from_workflow_sha256': hashlib.sha256(old.encode()).hexdigest(),
            'to_workflow_sha256': hashlib.sha256(new.encode()).hexdigest(), 'reviewers': ['astra']}]}
        texts = {('old', gate.WORKFLOW): old, ('new', gate.WORKFLOW): new,
                 ('old', gate.INSTRUCTIONS): 'instructions', ('new', gate.INSTRUCTIONS): 'instructions',
                 ('old', gate.REUSE_POLICY): '{}', ('new', gate.REUSE_POLICY): json.dumps(policy)}
        gh = FakeGH()
        gh.text = lambda path, ref: texts[ref, path]
        self.assertTrue(gate.same_reviewer_policy(gh, 'old', 'new', 'astra'))
        self.assertFalse(gate.same_reviewer_policy(gh, 'old', 'new', 'fable'))
        texts['new', gate.WORKFLOW] += ' later change'
        self.assertFalse(gate.same_reviewer_policy(gh, 'old', 'new', 'astra'))
        texts['new', gate.WORKFLOW] = new
        texts['new', gate.INSTRUCTIONS] += ' changed reviewer requirement'
        self.assertFalse(gate.same_reviewer_policy(gh, 'old', 'new', 'astra'))

    def test_compatibility_registry_change_invalidates_running_policy(self):
        gh = FakeGH()
        gh.text = lambda path, ref: ref if path == gate.REUSE_POLICY else 'unchanged'
        self.assertFalse(gate.same_policy(gh, 'old', 'new'))

    def test_override_respects_exact_reviewer_migration_without_model_calls(self):
        for migration in (True, False):
            with self.subTest(migration=migration):
                gh, app = FakeGH(), FakeApp()
                gh.permission = 'write'
                old = 'c' * 40
                pair = {'astra': envelope(policy_ref=old, read_prerequisites_complete=True),
                        'fable': envelope('fable', review=report(decision='changes_requested',
                            findings=[{'id': 'F1', 'location': 'p:1', 'objection': 'gap'}]))}
                command = comment('/protocol-b override ' + HEAD + ' 1-1-fable-F1 accepted limitation', 'collaborator')
                from test_gate import report_comment
                old_workflow, new_workflow = 'old-workflow', 'new-workflow'
                registry = {'schema': 'protocol-b-review-compatibility/v1', 'migrations': [{
                    'from_workflow_sha256': hashlib.sha256(old_workflow.encode()).hexdigest(),
                    'to_workflow_sha256': hashlib.sha256(new_workflow.encode()).hexdigest(),
                    'reviewers': ['astra']}]}
                def text(path, ref):
                    if path == gate.WORKFLOW:
                        return old_workflow if ref == old else new_workflow
                    if path == gate.REUSE_POLICY:
                        return '{}' if ref == old else json.dumps(registry)
                    return 'unchanged'
                gh.text = text
                compact = copy.deepcopy(pair['astra'])
                compact['review'].pop('report')
                compact['review'].pop('sources_read')
                app.prior({'astra': compact})
                gh.review_material = lambda row: (pair['astra'],
                    {'discussion': [], 'prior_findings': {}, 'overrides': {}}, original_input(gh), [])
                retry = {'issue': {'number': 1}, 'comment': comment('/protocol-b review', 'collaborator'),
                         'sender': {'login': 'collaborator'}}
                called = []
                def rejecting_fable(reviewer):
                    called.append(reviewer.family)
                    reviewer.history_read, reviewer.reads = True, [{'path': 'source.tex'}]
                    return pair['fable']['review']
                _, _, _, initial = run_pipeline(gh, app, event=retry, provider=rejecting_fable)
                self.assertEqual(called, ['fable'])
                self.assertEqual(initial['conclusion'], 'failure')
                published = json.loads(app.checks[20]['output']['text'])['reports']
                self.assertEqual(published['astra']['policy_ref'], old)
                self.assertEqual(published['fable']['policy_ref'], BASE)
                self.assertNotIn('report', published['astra']['review'])
                app = FakeApp()
                app.prior(published)
                gh.comments = [report_comment(v) for v in published.values()]
                command['body'] = command['body'].replace('1-1-fable-F1', '7-1-fable-F1')
                gh.comments.append(command)
                event = {'issue': {'number': 1}, 'comment': command, 'sender': {'login': 'collaborator'}}
                if not migration:
                    registry['migrations'][0]['reviewers'] = []
                with patch.object(gate, 'model_turn', side_effect=AssertionError('No provider call')):
                    _, _, errors, state = run_pipeline(gh, app, event=event,
                        provider=lambda reviewer: (_ for _ in ()).throw(AssertionError('No review')))
                self.assertEqual(state['conclusion'], 'success' if migration else 'failure')
                self.assertEqual(bool(errors), not migration)
                if migration:
                    self.assertIn('NOT outside reviewed', state['summary'])

    def test_absent_previous_or_current_registry_means_no_migration(self):
        for missing in (BASE, HEAD):
            with self.subTest(missing=missing):
                gh = gate.GitHub('x/y', 'fake')
                def get(path):
                    if gate.REUSE_POLICY in path and path.endswith(missing):
                        raise gate.RequestError({'status': 404, 'message': 'Not found'})
                    value = '{}' if gate.REUSE_POLICY in path else 'unchanged'
                    return {'type': 'file', 'size': len(value), 'encoding': 'base64',
                            'content': base64.b64encode(value.encode()).decode()}
                with patch.object(gh, 'call', side_effect=get):
                    self.assertEqual(gate.reuse_policy_text(gh, missing), '{}')
                    self.assertTrue(gate.same_policy(gh, BASE, HEAD))

    def test_non_missing_registry_failure_is_not_suppressed(self):
        gh = gate.GitHub('x/y', 'fake')
        with patch.object(gh, 'call', side_effect=gate.RequestError({'status': 403, 'message': 'Forbidden'})):
            with self.assertRaises(gate.RequestError):
                gate.reuse_policy_text(gh, BASE)


class WebEvidence(unittest.TestCase):
    def test_document_presence_is_reported_without_copying_source(self):
        output = [{'type': 'web_fetch_tool_result', 'tool_use_id': 'fetch', 'content': {
            'type': 'web_fetch_result', 'content': {'source': {'type': 'base64', 'data': 'PRIVATE_DOCUMENT_BYTES'}}}}]
        result = gate.web_response_observation(output, {'server_tool_use': {'web_fetch_requests': 2}}, 'response', 3)
        self.assertTrue(result['returned_results'][0]['document_payload_present'])
        self.assertEqual(result['unreturned_reported_fetches'], 1)
        self.assertNotIn('PRIVATE_DOCUMENT_BYTES', json.dumps(result))
        self.assertIn('not sent', result['next_request']['status'])

    def test_absent_result_identity_is_not_invented(self):
        result = gate.web_response_observation([], {'server_tool_use': {'web_fetch_requests': 12}}, 'response', 3)
        self.assertEqual(result['returned_results'], [])
        self.assertEqual(result['unreturned_reported_fetches'], 12)
        self.assertIn('identities and success are not observable', result['omission_note'])


if __name__ == '__main__':
    unittest.main()
