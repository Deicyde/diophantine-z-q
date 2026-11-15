"""Offline spending controls exercise the trusted embedded gate, with no API calls."""
import copy
import io
import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock, patch
from test_gate import gate, FakeGH, FakeApp, HEAD, BASE, APP_ID, report, envelope, comment, changed, run_pipeline


class Spending(unittest.TestCase):
    def tearDown(self):
        gate.configure_budget([])

    def blocked(self, gh, app=None, event=None):
        provider = Mock(side_effect=AssertionError('No review may start'))
        with patch.object(gate, 'model_turn') as request:
            result = run_pipeline(gh, app, event=event, provider=provider)
            request.assert_not_called()
        provider.assert_not_called()
        return result

    def command(self):
        return {'issue': {'number': 1}, 'comment': comment('/protocol-b review', 'collaborator'),
                'sender': {'login': 'collaborator'}}

    def test_outside_author_waits_for_current_collaborator_command(self):
        for permission in ['read', 'triage', 'none']:
            gh = FakeGH()
            gh.author_permission = permission
            _, app, _, state = self.blocked(gh)
            self.assertEqual(app.final['conclusion'], 'action_required')
            self.assertIn("awaiting a collaborator's /protocol-b review", state['summary'])
        gh = FakeGH()
        gh.author_permission, gh.permission = 'read', 'write'
        provider = Mock(return_value=report())
        _, app, errors, _ = run_pipeline(gh, provider=provider, event=self.command())
        self.assertEqual(errors, [])
        self.assertEqual(provider.call_count, 2)
        self.assertEqual(app.final['conclusion'], 'success')

    def test_dispatch_or_unauthorized_comment_cannot_start_outside_review(self):
        gh = FakeGH()
        gh.author_permission = 'read'
        self.blocked(gh, event={'inputs': {'pull_request': '1'}})
        _, app, _, _ = self.blocked(gh, event=self.command())
        self.assertFalse(app.created)

    def test_current_write_author_can_start_automatic_review(self):
        for permission in ['write', 'maintain', 'admin']:
            gh = FakeGH()
            gh.author_permission = permission
            provider = Mock(return_value=report())
            _, _, errors, state = run_pipeline(gh, provider=provider)
            self.assertEqual(errors, [])
            self.assertEqual(provider.call_count, 2)
            self.assertEqual(state['automatic_rounds'], 1)

    def test_failed_required_check_blocks_even_explicit_command(self):
        for event in [None, self.command()]:
            gh = FakeGH()
            gh.permission = 'write'
            gh.check_runs = [{'id': 2, 'name': 'Paper build', 'head_sha': HEAD,
                             'status': 'completed', 'conclusion': 'failure', 'app': {'id': 15368}}]
            _, app, _, state = self.blocked(gh, event=event)
            self.assertEqual(app.final['conclusion'], 'action_required')
            self.assertIn('fix failing checks first: Paper build', state['summary'])

    def test_nonrequired_failure_and_pending_check_do_not_block(self):
        gh = FakeGH()
        gh.check_runs = [{'id': 1, 'name': 'Paper build', 'head_sha': HEAD,
                         'status': 'in_progress', 'conclusion': None, 'app': {'id': 15368}},
                        {'id': 2, 'name': 'Optional experiment', 'head_sha': HEAD,
                         'status': 'completed', 'conclusion': 'failure', 'app': {'id': 15368}}]
        provider = Mock(return_value=report())
        _, _, errors, _ = run_pipeline(gh, provider=provider)
        self.assertEqual(errors, [])
        self.assertEqual(provider.call_count, 2)

    def test_new_failure_between_turns_prevents_another_provider_request(self):
        gh = FakeGH()
        review = gate.Review(gh, gh.pr, [], [], {}, {}, 'trusted', 'fable', 'local mathematical')
        def model(*args, **kwargs):
            gh.check_runs = [{'id': 2, 'name': 'Paper build', 'head_sha': HEAD,
                             'status': 'completed', 'conclusion': 'failure', 'app': {'id': 15368}}]
            return ([{'type': 'tool_use', 'id': 'h', 'name': 'read_history', 'input': {}}],
                    gate.MODELS['fable'], {}, 'fixture', 'tool_use')
        with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
             patch.object(gate, 'model_turn', side_effect=model) as provider:
            with self.assertRaisesRegex(RuntimeError, 'fix failing checks first'):
                review.run()
        self.assertEqual(provider.call_count, 1)

    def rounds(self, count=4):
        gh, app = FakeGH(), FakeApp()
        for i in range(1, count+1):
            past = str(i) * 40
            marker = {'number': 1, 'run': str(100+i), 'attempt': '1', 'started': True, 'trigger': 'automatic'}
            app.checks[i] = {'id': i, 'name': 'Protocol B / test review', 'head_sha': past,
                            'status': 'completed', 'conclusion': 'action_required', 'app': {'id': APP_ID},
                            'output': {'text': json.dumps({'schema': 'protocol-b-decisions/v1', 'head': past,
                                                          'review_round': marker, 'reports': {}})}}
            gh.comments.append(comment(gate.ROUND_MARKER + '\n```json\n' + json.dumps({'check': i}) + '\n```'))
        return gh, app

    def test_four_started_rounds_block_push_and_survive_force_push(self):
        gh, app = self.rounds()
        _, app, _, state = self.blocked(gh, app)
        self.assertEqual(state['automatic_rounds'], 4)
        self.assertIn('Four automatic', state['summary'])
        self.assertIn('4/4', app.final['output']['summary'])

    def test_fourth_round_runs_but_fifth_requires_command(self):
        gh, app = self.rounds(3)
        provider = Mock(return_value=report())
        _, app, errors, state = run_pipeline(gh, app, provider=provider)
        self.assertEqual(errors, [])
        self.assertEqual(provider.call_count, 2)
        self.assertEqual(state['automatic_rounds'], 4)
        gh, app = self.rounds(4)
        gh.permission = 'write'
        _, app, errors, state = run_pipeline(gh, app, provider=provider, event=self.command())
        self.assertEqual(errors, [])
        self.assertEqual(state['automatic_rounds'], 4)
        self.assertEqual(state['review_round']['trigger'], 'command')

    def test_forged_round_pointer_is_not_authority(self):
        gh, app = self.rounds()
        for c in app.checks.values():
            c['app']['id'] = 15368
        _, _, errors, state = run_pipeline(gh, app)
        self.assertEqual(errors, [])
        self.assertEqual(state['automatic_rounds'], 1)

    def test_legacy_app_reports_count_toward_automatic_limit(self):
        gh, app = self.rounds()
        gh.comments = []
        for i, check in app.checks.items():
            pair = {family: envelope(family, run=str(100+i), head=check['head_sha']) for family in gate.MODELS}
            check['output']['text'] = json.dumps({'schema': 'protocol-b-decisions/v1',
                                                  'head': check['head_sha'], 'reports': pair})
            gh.comments.append(comment(gate.MARKER + '\n```json\n' + json.dumps(pair['astra']) + '\n```'))
            gh.dispatched_runs[100+i] = {'event': 'pull_request_target', 'path': gate.WORKFLOW}
        _, _, _, state = self.blocked(gh, app)
        self.assertEqual(state['automatic_rounds'], 4)

    def test_reopen_ready_and_duplicate_sync_reuse_complete_same_policy(self):
        for action in ['reopened', 'ready_for_review', 'synchronize']:
            gh, app = FakeGH(), FakeApp()
            app.prior({'astra': envelope(), 'fable': envelope('fable')})
            _, app, errors, _ = self.blocked(gh, app, event={'pull_request': {'number': 1}, 'action': action})
            self.assertEqual(errors, [])
            self.assertFalse(app.created)

    def test_new_policy_or_incomplete_review_does_not_reuse(self):
        for incomplete in [False, True]:
            gh, app = FakeGH(), FakeApp()
            pair = {'astra': envelope(), 'fable': envelope('fable', complete=not incomplete)}
            app.prior(pair)
            provider = Mock(return_value=report())
            original = gate.same_policy
            with patch.object(gate, 'same_policy', side_effect=lambda gh, old, new: old == new):
                if not incomplete:
                    pair['astra']['policy_ref'] = 'e' * 40
                    app.prior(pair)
                _, _, errors, _ = run_pipeline(gh, app, provider=provider,
                    event={'pull_request': {'number': 1}, 'action': 'reopened'})
            self.assertEqual(errors, [])
            self.assertEqual(provider.call_count, 2)

    def test_profiles_follow_changed_paths_and_renames(self):
        for file in [changed('manuscripts/new.tex'), changed('archive/old.tex', previous_filename='manuscripts/old.tex')]:
            with patch.dict(os.environ, {'MANUSCRIPT_PROFILE': 'expanded'}):
                profile = gate.configure_budget([file])
            self.assertEqual(profile['context_token_budget'], 900000)
            body = gate.model_body('fable', 'trusted', [])
            self.assertEqual(body['tools'][-2]['max_uses'], 10)
            self.assertEqual(body['tools'][-1]['max_uses'], 20)
            self.assertEqual(body['tools'][-1]['max_content_tokens'], 50000)
        profile = gate.configure_budget([changed('docs/manuscripts/note.md')])
        self.assertEqual(profile['context_token_budget'], 400000)
        self.assertEqual(profile['fable_web_max_uses'], {'web_search': 3, 'web_fetch': 5})

    def test_initial_low_context_can_report_unreviewed_scope_but_not_accept(self):
        for decision in ['accept', 'changes_requested']:
            gh = FakeGH()
            review = gate.Review(gh, gh.pr, [], [], {}, {}, 'trusted', 'fable', 'local mathematical')
            review.input['material'] = 'x' * 280000
            result = report(decision=decision, sources_read=[],
                            report='Not reviewed: source statements and all consumers. The remaining context is insufficient; these checks remain open.',
                            findings=[{'id': 'INCOMPLETE', 'location': 'whole PR', 'objection': 'Required source review remains unfinished.'}])
            response = ([{'type': 'tool_use', 'id': 'finish', 'name': 'finish_review', 'input': result}],
                        gate.MODELS['fable'], {}, 'fixture', 'end_turn')
            with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
                 patch.object(gate, 'model_turn', return_value=response) as model:
                if decision == 'accept':
                    with self.assertRaises(ValueError):
                        review.run()
                else:
                    self.assertEqual(review.run()['decision'], 'changes_requested')
                self.assertEqual(model.call_args.args[1], 'trusted')
                self.assertTrue(any(gate.FINISH_NOW_INSTRUCTION in str(m.get('content', ''))
                                    for m in model.call_args.args[2] if m.get('role') == 'system'))

    def test_manuscript_profile_defaults_to_current_limits_and_scales_text(self):
        for value in ['', 'standard', 'expanded']:
            with patch.dict(os.environ, {'MANUSCRIPT_PROFILE': value}):
                profile = gate.configure_budget([changed('manuscripts/new.tex')])
            expanded = value == 'expanded'
            self.assertEqual(profile['context_token_budget'], 900000 if expanded else 400000)
            self.assertEqual(gate.TOOL_CHARACTER_BUDGET, 2700000 if expanded else 1200000)
            self.assertEqual(profile['fable_web_max_uses'],
                             {'web_search': 10, 'web_fetch': 20} if expanded else {'web_search': 3, 'web_fetch': 5})
            self.assertEqual(profile['fable_web_fetch_max_content_tokens'], 50000 if expanded else 20000)
        with patch.dict(os.environ, {'MANUSCRIPT_PROFILE': 'expanded'}):
            profile = gate.configure_budget([changed('docs/readme.md')])
        self.assertEqual(profile['context_token_budget'], 400000)
        self.assertEqual(gate.TOOL_CHARACTER_BUDGET, 1200000)
        with patch.dict(os.environ, {'MANUSCRIPT_PROFILE': 'typo'}):
            with self.assertRaisesRegex(ValueError, 'standard or expanded'):
                gate.configure_budget([changed('manuscripts/new.tex')])

    def test_unread_history_stays_unresolved_and_cannot_be_overridden(self):
        gh = FakeGH()
        prior_id = '1-1-astra-EARLIER'
        review = gate.Review(gh, gh.pr, [], [], {prior_id: {}}, {}, 'trusted', 'fable', 'local mathematical')
        review.input['material'] = 'x' * 280000
        decision = report(decision='changes_requested', sources_read=[],
                          report='Not reviewed: source statements and earlier findings. Remaining context does not suffice for this review.',
                          findings=[{'id': 'BUDGET', 'location': 'scope', 'objection': 'Review unfinished.'}],
                          prior_findings=[{'id': prior_id, 'resolution': 'resolved', 'reason': 'Model mistakenly assumes a repair.'}])
        output = [{'type': 'tool_use', 'name': 'finish_review', 'id': 'finish', 'input': decision}]
        with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
             patch.object(gate, 'model_turn', return_value=(output, gate.MODELS['fable'], {}, 'm', 'tool_use')):
            result = review.run()
        self.assertEqual(result['prior_findings'][0]['resolution'], 'unresolved')
        pair = {'astra': envelope(), 'fable': envelope('fable')}
        pair['fable'].update(review=result, finished_early=True, read_prerequisites_complete=False)
        with self.assertRaisesRegex(ValueError, 'missing source or history'):
            gate.overridden_decision(pair, {prior_id: {}, '1-1-fable-BUDGET': {}}, HEAD)
        gh, app, _, state = run_pipeline(FakeGH(), provider=Mock(return_value=result))
        self.assertIs(state['reports']['fable']['read_prerequisites_complete'], False)
        stored = json.loads(app.final['output']['text'])
        self.assertIs(stored['reports']['fable']['read_prerequisites_complete'], False)

    def test_failure_during_retry_backoff_prevents_second_provider_post(self):
        for family in gate.MODELS:
            gh = FakeGH()
            review = gate.Review(gh, gh.pr, [], [], {}, {}, 'trusted', family, 'local mathematical')
            url = 'https://api.openai.com/v1/responses' if family == 'astra' else 'https://api.anthropic.com/v1/messages'
            error = gate.urllib.error.HTTPError(url, 429, 'rate', {}, io.BytesIO(b'{}'))
            def fail_check(_delay):
                gh.check_runs = [{'id': 2, 'name': 'Paper build', 'head_sha': HEAD,
                                 'status': 'completed', 'conclusion': 'failure', 'app': {'id': 15368}}]
            with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
                 patch.dict(os.environ, {'OPENAI_API_KEY': 'fixture', 'ANTHROPIC_API_KEY': 'fixture'}), \
                 patch.object(gate.time, 'sleep', side_effect=fail_check), \
                 patch.object(gate.urllib.request, 'urlopen', side_effect=error) as provider:
                with self.assertRaisesRegex(RuntimeError, 'fix failing checks first'):
                    review.run()
            self.assertEqual(provider.call_count, 1)

    def test_low_context_preserves_signed_prefix_and_pause_continuation(self):
        for paused in [False, True]:
            gh = FakeGH()
            review = gate.Review(gh, gh.pr, [], [], {}, {}, 'trusted', 'fable', 'local mathematical')
            review.input['material'] = 'x' * 230000
            review.reads, review.history_read = [{'path': 'earlier-source'}], True
            signed = {'type': 'thinking', 'thinking': 'Earlier source analysis.', 'signature': 'immutable-signature'}
            initial = [signed, {'type': 'text', 'text': 'x' * 50000}]
            decision = report(decision='changes_requested',
                              report='Not reviewed: the remaining source application and its exact hypotheses. This review requests changes because that required check is incomplete.',
                              findings=[{'id': 'BUDGET', 'location': 'application', 'objection': 'Required review incomplete.'}])
            seen = []
            def model(family, instructions, conversation, **kwargs):
                body = copy.deepcopy(gate.model_body(family, instructions, conversation))
                seen.append(body)
                if len(seen) == 1:
                    output, stop = initial, 'pause_turn' if paused else 'end_turn'
                else:
                    self.assertEqual(body['system'], seen[0]['system'])
                    self.assertEqual(body['tools'], seen[0]['tools'])
                    self.assertEqual(body['messages'][:len(seen[-2]['messages'])], seen[-2]['messages'])
                    self.assertEqual(body['messages'][1], {'role': 'assistant', 'content': initial})
                    if paused and len(seen) == 2:
                        self.assertEqual(body['messages'][-1], {'role': 'assistant', 'content': initial})
                        output, stop = [{'type': 'tool_use', 'id': 'history', 'name': 'read_history', 'input': {}}], 'tool_use'
                    else:
                        self.assertEqual(body['messages'][-2]['role'], 'user')
                        self.assertEqual(body['messages'][-1]['role'], 'system')
                        self.assertIn(gate.FINISH_NOW_INSTRUCTION, body['messages'][-1]['content'])
                        output, stop = [{'type': 'tool_use', 'id': 'finish', 'name': 'finish_review', 'input': decision}], 'tool_use'
                return output, gate.MODELS[family], {}, 'fixture', stop
            with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
                 patch.dict(os.environ, {'GITHUB_RUN_ID': '1', 'GITHUB_RUN_ATTEMPT': '1'}), \
                 patch.object(gate, 'model_turn', side_effect=model):
                self.assertEqual(review.run()['decision'], 'changes_requested')
            self.assertEqual(len(seen), 3 if paused else 2)


if __name__ == '__main__':
    unittest.main()
