"""Acceptance-side regressions for objections and original report delivery."""
import copy
import json
import threading
import unittest
from unittest.mock import Mock, patch
from test_gate import gate, FakeGH, FakeApp, HEAD, BASE, report, envelope, comment, report_comment, run_pipeline
from test_continuity import accepting, stored


class AcceptanceHistory(unittest.TestCase):
    def direct_comment_override(self, include_finding):
        gh, app = FakeGH(), FakeApp()
        gh.permission = 'admin'
        pair = {f: envelope(f, complete=False, runtime_scope_record=True, review=report(
            decision='not_reviewed', scope_complete=False, not_reviewed=['No model ran'])) for f in gate.MODELS}
        stored(app, gh, pair, ident=5)
        stored(app, gh, {}, ident=6)
        objection = envelope(run='6', review=report(decision='changes_requested',
            findings=[{'id': 'F1', 'objection': 'An actual later objection, with no final App record.'}]))
        gh.comments.append(report_comment(objection))
        ids = ['scope-1-1-astra', 'scope-1-1-fable']
        if include_finding:
            ids.append('6-1-astra-F1')
        gh.comments += [comment('/protocol-b override '+HEAD+' '+ident+' Explicit decision', 'collaborator') for ident in ids]
        event = {'issue': {'number': 1}, 'comment': gh.comments[-1], 'sender': {'login': 'collaborator'}}
        provider = Mock(side_effect=AssertionError('Override must not call a model'))
        with patch.object(gate, 'model_turn', side_effect=AssertionError('No provider request')):
            result = run_pipeline(gh, app, event=event, provider=provider)
        provider.assert_not_called()
        return result

    def test_direct_scope_override_cannot_skip_unfinalized_report_comment(self):
        gh, app, _, state = self.direct_comment_override(False)
        self.assertEqual(app.final['conclusion'], 'failure')
        self.assertIn('6-1-astra-F1', state['summary'])
        self.assertFalse(gh.merge_requests)
        values = [e['carried_findings']['6-1-astra-F1'] for e in state['reports'].values()
                  if '6-1-astra-F1' in e.get('carried_findings', {})]
        self.assertEqual(values[0]['origin_reviewer'], 'history')
        self.assertIn('not authenticated model identity', values[0]['reason'])

    def test_direct_override_can_address_comment_claim_separately(self):
        _, app, errors, state = self.direct_comment_override(True)
        self.assertEqual(errors, [])
        self.assertEqual(app.final['conclusion'], 'success')
        self.assertIn('6-1-astra-F1', state['overrides'])

    def returned_head(self):
        gh, app = FakeGH(), FakeApp()
        stored(app, gh, {f: accepting(f) for f in gate.MODELS}, ident=5)
        other = 'c'*40
        rejected = envelope(head=other, run='6', complete=False, review=report(
            decision='changes_requested', scope_complete=False, not_reviewed=['Execution interrupted'],
            findings=[{'id':'F1','objection':'An unchanged dependency has a counterexample.'}]))
        stored(app, gh, {'astra': rejected}, ident=6, head=other)
        gh.permission = 'write'
        event = {'issue': {'number': 1}, 'comment': comment('/protocol-b review', 'collaborator'),
                 'sender': {'login': 'collaborator'}}
        return gh, app, event

    def test_return_to_accepted_head_needs_supplement_for_app_only_objection(self):
        gh, app, event = self.returned_head()
        seen = []
        def provider(reviewer):
            seen.append({**reviewer.input, 'prior_findings': reviewer.tool('read_history', {})['earlier_findings']})
            reviewer.history_read = True
            reviewer.reads = [{'path':'p.tex','revision':HEAD,'start':1,'count':1}]
            return report(decision='changes_requested', prior_findings=[{
                'id':'6-1-astra-F1','resolution':'unresolved','reason':'The counterexample still applies.'}])
        gh, app, _, state = run_pipeline(gh, app, event=event, provider=provider)
        self.assertTrue(seen)
        self.assertTrue(all('retained_acceptance' in value for value in seen))
        self.assertTrue(all('6-1-astra-F1' in value['prior_findings'] for value in seen))
        self.assertEqual(app.final['conclusion'], 'failure')
        self.assertIn('6-1-astra-F1', state['summary'])
        self.assertFalse(gh.merge_requests)

    def test_grounded_supplement_can_resolve_app_only_objection(self):
        gh, app, event = self.returned_head()
        def provider(reviewer):
            reviewer.history_read = True
            reviewer.reads = [{'path':'p.tex','revision':HEAD,'start':1,'count':1}]
            return report(prior_findings=[{'id':'6-1-astra-F1','resolution':'resolved',
                'reason':'Read p.tex:1 and the dependency; the alleged omitted premise is explicit.'}])
        _, app, errors, state = run_pipeline(gh, app, event=event, provider=provider)
        self.assertEqual(errors, [])
        self.assertEqual(app.final['conclusion'], 'success')
        self.assertFalse(any(e.get('carried_findings') for e in state['reports'].values()))

    def test_both_families_ground_dispositions_of_new_app_only_claim(self):
        gh, app, event = self.returned_head()
        payload = json.loads(app.checks[6]['output']['text'])
        old = payload['reports'].pop('astra')
        old.update(reviewer='fable', model=gate.MODELS['fable'])
        payload['reports']['fable'] = old
        app.checks[6]['output']['text'] = json.dumps(payload)
        seen = []
        def provider(reviewer):
            seen.append(reviewer.family)
            reviewer.history_read = True
            reviewer.reads = [{'path':'p.tex','revision':HEAD,'start':1,'count':1}]
            return report(prior_findings=[{'id':'6-1-fable-F1','resolution':'resolved',
                'reason':'Read p.tex:1 and verified the purported counterexample violates its premise.'}])
        _, app, errors, _ = run_pipeline(gh, app, event=event, provider=provider)
        self.assertEqual(errors, [])
        self.assertEqual(set(seen), set(gate.MODELS))
        self.assertEqual(app.final['conclusion'], 'success')

    def test_acceptance_delivery_failure_retried_at_publish_without_model(self):
        gh = FakeGH(); original = gh.call; attempts = []
        def call(path, method='GET', data=None):
            if method == 'POST' and path.endswith('/comments') and data['body'].startswith(gate.MARKER):
                value = json.loads(data['body'].split('```json\n')[1].split('\n```')[0])
                if value['reviewer'] == 'astra':
                    attempts.append(value)
                    if len(attempts) == 1:
                        raise RuntimeError('Temporary comment outage')
            return original(path, method, data)
        gh.call = call
        provider = Mock(return_value=report())
        _, app, errors, state = run_pipeline(gh, provider=provider)
        self.assertEqual(errors, [])
        self.assertEqual(provider.call_count, 2)
        self.assertEqual(len(attempts), 2)
        self.assertEqual(app.final['conclusion'], 'success')
        self.assertEqual(state['reports']['astra']['report_publication']['status'], 'posted')

    def test_persistent_acceptance_delivery_failure_is_visible_and_cannot_merge(self):
        gh = FakeGH(); original = gh.call
        def call(path, method='GET', data=None):
            if method == 'POST' and path.endswith('/comments') and data['body'].startswith(gate.MARKER):
                raise RuntimeError('Persistent comment outage')
            return original(path, method, data)
        gh.call = call
        value = report(findings=[{'id':'N1','kind':'editorial','severity':'note','objection':'Optional wording'}])
        gh, app, _, state = run_pipeline(gh, provider=Mock(return_value=value))
        self.assertEqual(app.final['conclusion'], 'failure')
        self.assertFalse(gh.merge_requests)
        self.assertIn('report publication failed; no merge', state['summary'])
        saved = json.loads(app.final['output']['text'])['reports']
        for e in saved.values():
            self.assertTrue(e['complete'])
            self.assertEqual(e['review']['decision'], 'accept')
            self.assertEqual(e['report_publication']['status'], 'failed')
            self.assertIn('PR report delivery is unavailable', e['nonblocking_notes_omitted']['location'])

    def test_optional_metadata_failure_still_posts_supplement_with_identity(self):
        gh, app, event = self.returned_head()
        def provider(reviewer):
            reviewer.history_read = True
            reviewer.reads = [{'path':'p.tex','revision':HEAD,'start':1,'count':1}]
            return report(prior_findings=[{'id':'6-1-astra-F1','resolution':'resolved','reason':'Verified source p.tex:1.'}])
        with patch.object(gate, 'optional_reuse_binding', side_effect=RuntimeError('Metadata unavailable')):
            _, app, errors, state = run_pipeline(gh, app, event=event, provider=provider)
        self.assertEqual(errors, [])
        self.assertEqual(app.final['conclusion'], 'success')
        fresh = [e for e in state['reports'].values() if e['run'] == '7']
        self.assertTrue(fresh)
        for e in fresh:
            self.assertIn('supplements_review', e)
            self.assertIn('retained_source_evidence', e)
            self.assertIsNone(e['reuse_binding'])
            self.assertEqual(e['report_publication']['status'], 'posted')

    def test_uncertain_post_reconciles_exact_comment_before_retry(self):
        gh = FakeGH(); original = gh.call; attempts = []
        def call(path, method='GET', data=None):
            if method == 'POST' and path.endswith('/comments') and data['body'].startswith(gate.MARKER):
                attempts.append(data['body'])
                gh.comments.append(comment(data['body']))
                raise RuntimeError('Response lost after server stored comment')
            return original(path, method, data)
        gh.call = call
        def provider(reviewer):
            reviewer.history_read = True
            reviewer.reads = [{'path':'p.tex','revision':HEAD,'start':1,'count':1}]
            return report()
        _, app, errors, state = run_pipeline(gh, provider=provider)
        self.assertEqual(errors, [])
        self.assertEqual(len(attempts), 2)
        self.assertEqual(app.final['conclusion'], 'success')
        self.assertTrue(all(e['report_publication']['status'] == 'posted' for e in state['reports'].values()))

    def test_final_publication_reconciles_claim_after_ordinary_acceptance(self):
        gh = FakeGH(); original = gh.call
        def call(path, method='GET', data=None):
            if path == '/pulls/1' and gh.pr_calls == 2:
                gh.comments.append(report_comment(envelope(run='9', review=report(
                    decision='changes_requested', findings=[{'id':'LATE','objection':'Late report claim.'}]))))
            return original(path, method, data)
        gh.call = call
        gh, app, _, state = run_pipeline(gh)
        self.assertEqual(app.final['conclusion'], 'failure')
        self.assertIn('9-1-astra-LATE', state['summary'])
        self.assertFalse(gh.merge_requests)

    def failed_publication_round(self):
        gh = FakeGH(); original = gh.call; original_bodies = []
        def call(path, method='GET', data=None):
            if method == 'POST' and path.endswith('/comments') and data['body'].startswith(gate.MARKER):
                original_bodies.append(data['body'])
                raise RuntimeError('Original report was never stored')
            return original(path, method, data)
        gh.call = call
        def provider(reviewer):
            reviewer.history_read = True
            reviewer.reads = [{'path':'p.tex','revision':HEAD,'start':1,'count':1}]
            return report(report='Distinctive full review prose.', sources_read=['Actual source p.tex:1'],
                findings=[{'id':'N1','severity':'note','kind':'editorial','location':'p.tex:1',
                           'objection':'Distinctive optional note.'}])
        _, app, _, _ = run_pipeline(gh, provider=provider)
        saved = json.loads(app.final['output']['text'])['reports']
        self.assertTrue(all('report' not in e['review'] for e in saved.values()))
        return saved, list(dict.fromkeys(original_bodies))

    def test_later_run_cannot_republish_compact_record_as_original_report(self):
        saved, _ = self.failed_publication_round()
        original_hashes = {f:e['report_publication']['sha256'] for f,e in saved.items()}
        gh, app = FakeGH(), FakeApp();stored(app, gh, saved, ident=5)
        gh.permission = 'write'
        event = {'issue':{'number':1},'comment':comment('/protocol-b review','collaborator'),
                 'sender':{'login':'collaborator'}}
        provider = Mock(side_effect=AssertionError('Keep completed review, do not re-ask models'))
        _, app, _, state = run_pipeline(gh, app, event=event, provider=provider)
        provider.assert_not_called()
        self.assertEqual(app.final['conclusion'], 'failure')
        self.assertFalse(any(p['body'].startswith(gate.MARKER) for p in gh.posts))
        for f,e in state['reports'].items():
            self.assertEqual(e['report_publication']['sha256'], original_hashes[f])
            self.assertIn('Full original report is absent', e['report_publication']['error'])
        self.assertFalse(gh.merge_requests)

    def test_later_run_can_reconcile_already_arrived_full_original_comment(self):
        saved, bodies = self.failed_publication_round()
        gh, app = FakeGH(), FakeApp();stored(app, gh, saved, ident=5)
        gh.comments.extend(comment(body) for body in bodies)
        for body in bodies:
            self.assertIn('Distinctive full review prose.', body)
            self.assertIn('Actual source p.tex:1', body)
            self.assertIn('Distinctive optional note.', body)
        gh.permission = 'write'
        event = {'issue':{'number':1},'comment':comment('/protocol-b review','collaborator'),
                 'sender':{'login':'collaborator'}}
        provider = Mock(side_effect=AssertionError('No second model review'))
        _, app, errors, state = run_pipeline(gh, app, event=event, provider=provider)
        provider.assert_not_called()
        self.assertEqual(errors, [])
        self.assertEqual(app.final['conclusion'], 'success')
        self.assertFalse(any(p['body'].startswith(gate.MARKER) for p in gh.posts))
        self.assertTrue(all(e['report_publication']['status'] == 'posted' for e in state['reports'].values()))

    def test_failure_comment_error_does_not_drop_completed_peer_verdict(self):
        gh = FakeGH(); original = gh.call; failed = threading.Event()
        def call(path, method='GET', data=None):
            if method == 'POST' and path.endswith('/comments') and data['body'].startswith(gate.MARKER):
                value = json.loads(data['body'].split('```json\n')[1].split('\n```')[0])
                if value['reviewer'] == 'astra' and not value['complete'] and not failed.is_set():
                    failed.set()
                    raise RuntimeError('Failure-comment POST failed')
            return original(path, method, data)
        gh.call = call
        def provider(reviewer):
            if reviewer.family == 'astra':
                raise RuntimeError('First reviewer interrupted')
            if not failed.wait(3):
                raise AssertionError('Expected the first failure-comment attempt before peer finishes')
            reviewer.history_read = True
            reviewer.reads = [{'path':'p.tex','revision':HEAD,'start':1,'count':1}]
            return report(decision='changes_requested', findings=[{
                'id':'F1','location':'p.tex:1','objection':'The peer delivered an actual counterexample.'}])
        _, app, _, state = run_pipeline(gh, provider=provider)
        self.assertTrue(failed.is_set())
        self.assertEqual(app.final['conclusion'], 'failure')
        saved = json.loads(app.final['output']['text'])['reports']
        self.assertTrue(saved['fable']['complete'])
        self.assertEqual(saved['fable']['review']['findings'][0]['id'], 'F1')
        self.assertFalse(saved['astra']['complete'])
        self.assertEqual(saved['astra']['report_publication']['status'], 'posted')
        scopes = {item['id']:{} for item in state['scope_items']}
        with self.assertRaisesRegex(ValueError, '7-1-fable-F1'):
            gate.overridden_decision(saved, scopes, HEAD)


if __name__ == '__main__':
    unittest.main()
