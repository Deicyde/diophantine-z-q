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

from test_gate import APP_ID, BASE, HEAD, FakeApp, FakeGH, comment, envelope, gate, report, run_pipeline


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
        gh.review_material = lambda row: (copy.deepcopy(accepted), {'discussion': [], 'prior_findings': {}, 'overrides': {}})
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
                                              BASE, {'new-F1': {}}, {}, [])
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
                                                      BASE, {}, {}, discussion)
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
                                                 {'discussion': [], 'prior_findings': {}, 'overrides': {}})
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
        gh = gate.GitHub('x/y', 'fake')
        def get(path):
            if path == '/actions/runs/1':
                return {'id': 1, 'path': gate.WORKFLOW, 'event': 'pull_request_target', 'head_sha': HEAD, 'run_attempt': 1}
            if path == '/actions/runs/1/artifacts?per_page=100&page=1':
                return {'artifacts': [{'id': 20, 'name': 'protocol-b-1-1', 'expired': False}]}
            raise AssertionError(path)
        with patch.object(gh, 'call', side_effect=get), patch.object(gate.urllib.request, 'build_opener') as opener:
            opener.return_value.open.return_value = io.BytesIO(buf.getvalue())
            self.assertEqual(gh.review_material(compact), (full, context))
        altered = copy.deepcopy(compact)
        altered['review']['not_outside_reviewed'] = ['Different scope']
        with patch.object(gh, 'call', side_effect=get), patch.object(gate.urllib.request, 'build_opener') as opener:
            opener.return_value.open.return_value = io.BytesIO(buf.getvalue())
            with self.assertRaisesRegex(ValueError, 'does not match'):
                gh.review_material(altered)

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
