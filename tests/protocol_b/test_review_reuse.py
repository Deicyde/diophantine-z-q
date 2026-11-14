"""Authenticated completed-review reuse; no provider or GitHub requests."""
import copy
import hashlib
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from test_gate import APP_ID, BASE, HEAD, FakeApp, FakeGH, comment, envelope, gate, report, run_pipeline


class Reuse(unittest.TestCase):
    def fixtures(self):
        gh, app = FakeGH(), FakeApp()
        gh.permission = 'write'
        accepted = envelope(read_prerequisites_complete=True)
        failed = envelope('fable', complete=False, review=report(decision='changes_requested'))
        app.prior({'astra': accepted, 'fable': failed})
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
                                              BASE, {'new-F1': {}}, {})
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
