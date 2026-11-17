"""Offline guards for the separately dispatched live reservation test."""
import copy
import importlib.util
import json
import unittest
from unittest.mock import Mock, patch

import test_gate as tg

spec = importlib.util.spec_from_file_location("live_admission_test", tg.ROOT/".github/scripts/test_protocol_b_admission.py")
live = importlib.util.module_from_spec(spec)
spec.loader.exec_module(live)


class LiveAdmissionTest(unittest.TestCase):
    def setUp(self):
        self.env = {"MODE":"test", "GITHUB_REPOSITORY":live.REPO, "GITHUB_REF":"refs/heads/main",
                    "GITHUB_EVENT_NAME":"workflow_dispatch", "GITHUB_SHA":"a"*40, "APP_ID":"42",
                    "GITHUB_RUN_ID":"123", "GITHUB_RUN_ATTEMPT":"1"}
        self.pr = {"number":69, "state":"closed", "merged":False, "user":{"id":12},
                   "head":{"sha":"b"*40}, "base":{"sha":"c"*40,"repo":{"full_name":live.REPO}}}
        self.gh, self.app = Mock(), Mock()
        self.events, self.saved = [], {}
        self.comment, self.check = {}, {}
        self.gh.call.side_effect = lambda path: self.pr if path == '/pulls/69' else self.comment
        self.app.call.side_effect = lambda path: self.check

    def once(self, client, path, method, data):
        self.events.append((client,path,method,copy.deepcopy(data)))
        if client is self.gh:
            self.assertEqual((path,method),('/issues/69/comments','POST'))
            self.comment.update(id=88,body=data['body'],created_at='2026-11-17T00:00:00Z',
                                updated_at='2026-11-17T00:00:00Z',user={'login':'github-actions[bot]'},
                                issue_url='https://api.github.com/repos/'+live.REPO+'/issues/69',
                                html_url='https://github.com/'+live.REPO+'/pull/69#issuecomment-88')
            return copy.deepcopy(self.comment)
        self.assertIs(client,self.app)
        self.assertEqual((path,method),('/check-runs','POST'))
        self.check.update(copy.deepcopy(data),id=99,app={'id':42})
        return copy.deepcopy(self.check)

    def run_case(self):
        with patch.object(tg.gate,'outside_api_once',side_effect=self.once), \
             patch.object(tg.gate,'outside_model_once',side_effect=AssertionError('No triage request')), \
             patch.object(tg.gate,'model_turn',side_effect=AssertionError('No reviewer request')):
            return live.exercise(tg.gate,self.gh,self.app,self.env,
                                 lambda name,value:self.saved.update({name:copy.deepcopy(value)}))

    def test_actual_production_reservation_helper_posts_intent_and_reads_back(self):
        originals = tg.gate.OUTSIDE_MARKER,tg.gate.OUTSIDE_CHECK
        result=self.run_case()
        self.assertEqual(len(self.events),2)
        self.assertEqual(result['provider_requests'],0)
        self.assertFalse(result['full_admission_tested'])
        self.assertTrue(self.comment['body'].startswith(live.TEST_MARKER))
        self.assertFalse(self.comment['body'].startswith(originals[0]))
        self.assertEqual(self.check['name'],live.TEST_CHECK)
        self.assertNotEqual(self.check['name'],originals[1])
        self.assertEqual(self.check['conclusion'],'neutral')
        self.assertEqual((tg.gate.OUTSIDE_MARKER,tg.gate.OUTSIDE_CHECK),originals)
        self.gh.call.assert_any_call('/issues/comments/88')
        self.app.call.assert_any_call('/check-runs/99')
        intent=json.loads(self.check['output']['text'])['intent']
        self.assertEqual((intent['number'],intent['head'],intent['policy']),(69,'b'*40,'a'*40))

    def test_test_intent_is_ignored_by_the_live_quota_scan(self):
        from test_outside_admission import Ledger
        ledger = Ledger()
        self.run_case()
        ledger.comments[ledger.pr['number']] = [self.comment]
        ledger.checks = [self.check]
        self.assertEqual(ledger.read(), [])

    def test_loader_uses_the_current_embedded_reservation_code(self):
        import hashlib
        path = tg.ROOT/'.github/workflows/protocol-b.yml'
        loaded, digest = live.load_program(path)
        self.assertEqual(digest, hashlib.sha256(path.read_bytes()).hexdigest())
        self.assertEqual(loaded.outside_reserve.__code__.co_code,
                         tg.gate.outside_reserve.__code__.co_code)

    def test_wrong_mode_branch_event_or_repo_writes_nothing(self):
        for key,value in [('MODE','live'),('GITHUB_REF','refs/heads/probe'),
                          ('GITHUB_EVENT_NAME','pull_request'),('GITHUB_REPOSITORY','other/repo')]:
            with self.subTest(key=key),patch.dict(self.env,{key:value}):
                with self.assertRaises(ValueError):self.run_case()
                self.assertFalse(self.events)

    def test_active_or_merged_test_pr_writes_nothing(self):
        for key,value in [('state','open'),('merged',True),('number',70)]:
            with self.subTest(key=key),patch.dict(self.pr,{key:value}):
                with self.assertRaises(ValueError):self.run_case()
                self.assertFalse(self.events)

    def test_unconfirmed_first_write_is_not_retried_or_followed_by_app_write(self):
        originals=tg.gate.OUTSIDE_MARKER,tg.gate.OUTSIDE_CHECK
        attempt=Mock(side_effect=RuntimeError('Uncertain write'))
        with patch.object(tg.gate,'outside_api_once',attempt):
            with self.assertRaises(RuntimeError):
                live.exercise(tg.gate,self.gh,self.app,self.env,
                              lambda name,value:self.saved.update({name:copy.deepcopy(value)}))
        attempt.assert_called_once()
        self.assertEqual(self.saved['write-events.json'][0]['state'],'unconfirmed')
        self.assertEqual((tg.gate.OUTSIDE_MARKER,tg.gate.OUTSIDE_CHECK),originals)

    def test_mismatched_readback_fails(self):
        self.app.call.side_effect=lambda path:{**self.check,'app':{'id':43}}
        with self.assertRaisesRegex(ValueError,'readback mismatch'):self.run_case()

    def test_admission_job_and_live_test_both_have_pull_request_write(self):
        admission=tg.workflow.split('  outside_admission:\n',1)[1].split('  kernel_preflight:\n',1)[0]
        self.assertIn('      pull-requests: write',admission)
        workflow=(tg.ROOT/'.github/workflows/protocol-b-admission-test.yml').read_text()
        self.assertIn("if: github.ref == 'refs/heads/main'",workflow)
        self.assertIn('      pull-requests: write',workflow)
        self.assertIn('          MODE: test',workflow)
        self.assertNotIn('OPENAI_API_KEY',workflow)
        self.assertNotIn('ANTHROPIC_API_KEY',workflow)
        self.assertNotIn('contents: write',workflow)
        self.assertNotIn('pull_request:',workflow)


if __name__ == '__main__':unittest.main()
