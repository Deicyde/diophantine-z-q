import json
import unittest
from unittest.mock import Mock, patch

from test_gate import gate, FakeGH, changed, comment, report, run_pipeline
import test_spend


class LightProfile(unittest.TestCase):
    def docs(self, gh):
        original = gh.pages
        gh.pages = lambda path: [changed('docs/building.md')] if path.endswith('/files') else original(path)
        return gh

    def test_focused_documentation_and_outside_authors_qualify(self):
        self.assertEqual(gate.review_profile([changed('docs/building.md')], True)['name'], 'light')
        self.assertEqual(gate.review_profile([changed('p.tex')], False)['name'], 'light')
        self.assertEqual(gate.review_profile([changed('p.tex')], True)['name'], 'full')

    def test_sensitive_mixed_renamed_large_and_incomplete_diffs_remain_full(self):
        cases = [[changed(path)] for path in (
            '.github/workflows/protocol-b.yml', 'docs/research-review/README.md',
            'docs/audit-history/PROTOCOL.md', 'docs/release-policy.md',
            'docs/theorem-application-audit/README.md',
            'docs/quartic-9625/verification/reviews/inventory.md',
            'docs/manuscript-revisions/version14/GUIDE.md', 'docs/reviews/example.md',
            'docs/research/example.md', 'docs/degree8-original/README.md',
            'docs/kernel-audits/example.md', 'docs/revision-2.md',
            'docs/effective-dirichlet-plan.md', 'docs/unclassified.md',
            'docs/current-manuscript-build.md', 'docs/lean-contributions.md',
            'research/version18/README.md', 'manuscripts/quartic_v18.tex', 'AGENTS.md')]
        cases += [[changed('docs/building.md'), changed('script.py')],
                  [changed('docs/building.md', previous_filename='manuscripts/quartic_v18.tex', status='renamed')],
                  [changed('docs/building.md', additions=500)],
                  [changed('docs/building.md')]*6, []]
        missing = changed('docs/building.md'); missing.pop('patch')
        cases.append([missing])
        for files in cases:
            with self.subTest(files=files):
                self.assertEqual(gate.review_profile(files, True)['name'], 'full')

    def test_consistent_patch_exercises_the_200_line_boundary(self):
        for additions, expected in ((100, 'light'), (101, 'full')):
            deletions = 100
            diff = f'@@ -1,{deletions} +1,{additions} @@\n'
            diff += '\n'.join(['-old'] * deletions + ['+new'] * additions)
            files = [changed('docs/building.md', diff=diff,
                             additions=additions, deletions=deletions)]
            with self.subTest(changed_lines=additions + deletions):
                self.assertEqual(gate.review_profile(files, True)['name'], expected)

    def test_record_changes_keep_full_profile_after_first_paid_round(self):
        for path in ('docs/theorem-application-audit/README.md',
                     'docs/quartic-9625/verification/reviews/inventory.md'):
            with self.subTest(path=path):
                gh, app = test_spend.Spending().rounds(1)
                original = gh.pages
                gh.pages = lambda endpoint: [changed(path)] if endpoint.endswith('/files') else original(endpoint)
                provider = Mock(return_value=report())
                _, app, errors, state = run_pipeline(gh, app, provider=provider)
                self.assertEqual(errors, [])
                self.assertEqual(state['review_profile']['name'], 'full')
                self.assertEqual(state['paid_rounds'], 2)
                self.assertEqual(provider.call_count, 2)
                self.assertEqual(app.final['conclusion'], 'success')

    def test_first_light_round_calls_both_reviewers_and_can_accept(self):
        provider = Mock(return_value=report())
        _, app, errors, state = run_pipeline(self.docs(FakeGH()), provider=provider)
        self.assertEqual(errors, [])
        self.assertEqual(provider.call_count, 2)
        self.assertEqual(state['review_profile']['name'], 'light')
        self.assertEqual(state['paid_rounds'], 1)
        self.assertEqual(app.final['conclusion'], 'success')
        payload = json.loads(app.final['output']['text'])
        self.assertEqual(payload['review_profile']['name'], 'light')
        self.assertEqual(payload['paid_rounds'], 1)

    def test_one_started_round_blocks_automatic_repeat_even_if_first_was_explicit(self):
        for trigger in ('automatic', 'command'):
            with self.subTest(trigger=trigger):
                gh, app = test_spend.Spending().rounds(1)
                value = json.loads(app.checks[1]['output']['text'])
                value['review_round']['trigger'] = trigger
                app.checks[1]['output']['text'] = json.dumps(value)
                provider = Mock(side_effect=AssertionError('No paid review'))
                with patch.object(gate, 'model_turn', side_effect=AssertionError('No provider request')):
                    _, app, _, state = run_pipeline(self.docs(gh), app, provider=provider)
                provider.assert_not_called()
                self.assertEqual(state['paid_rounds'], 1)
                self.assertEqual(app.final['conclusion'], 'action_required')
                self.assertIn('one paid round', state['summary'])
                self.assertIn('only an admin may override', state['summary'])

    def test_accept_then_changed_head_needs_explicit_review_and_cannot_merge(self):
        gh = self.docs(FakeGH())
        _, app, errors, state = run_pipeline(gh, provider=Mock(return_value=report()))
        self.assertEqual(errors, [])
        self.assertEqual(app.final['conclusion'], 'success')
        gh.comments.extend(comment(p['body']) for p in gh.posts)
        gh.posts.clear()
        gh.pr['head']['sha'] = 'c' * 40
        provider = Mock(side_effect=AssertionError('No automatic second review'))
        with patch.object(gate, 'model_turn', side_effect=AssertionError('No provider request')), \
             patch.object(gate, 'merge_and_dispatch', side_effect=AssertionError('No merge')):
            _, app, _, state = run_pipeline(gh, app, provider=provider)
        provider.assert_not_called()
        self.assertEqual(app.final['conclusion'], 'action_required')
        self.assertEqual(app.checks[20]['head_sha'], 'c' * 40)
        self.assertFalse(gh.merge_requests)
        self.assertIsNone(gh.graphql)
        self.assertIn('This PR had its one automatic review. To have changes reviewed, ask a maintainer to post /protocol-b review.', state['summary'])

    def test_collaborator_fork_keeps_full_profile_for_manuscript(self):
        gh = FakeGH()
        gh.pr['head']['repo'] = {'fork': True}
        gh.author_permission = 'write'
        original = gh.pages
        gh.pages = lambda path: [changed('manuscripts/new.tex')] if path.endswith('/files') else original(path)
        _, app, errors, state = run_pipeline(gh, provider=Mock(return_value=report()))
        self.assertEqual(errors, [])
        self.assertEqual(state['review_profile']['name'], 'full')
        self.assertEqual(app.final['conclusion'], 'success')

    def test_write_collaborator_can_explicitly_choose_another_review(self):
        gh, app = test_spend.Spending().rounds(1)
        gh.permission = 'write'
        provider = Mock(return_value=report())
        _, app, errors, state = run_pipeline(self.docs(gh), app, provider=provider, event=test_spend.Spending().command())
        self.assertEqual(errors, [])
        self.assertEqual(provider.call_count, 2)
        self.assertEqual(state['paid_rounds'], 2)
        self.assertEqual(app.final['conclusion'], 'success')

    def test_outside_author_still_requires_current_write_authorization(self):
        gh = self.docs(FakeGH())
        gh.author_permission = 'read'
        provider = Mock(side_effect=AssertionError('No review without collaborator command'))
        with patch.object(gate, 'model_turn', side_effect=AssertionError('No provider request')):
            _, app, _, state = run_pipeline(gh, provider=provider)
        provider.assert_not_called()
        self.assertIn("awaiting a collaborator's /protocol-b review", state['summary'])
        self.assertEqual(app.final['conclusion'], 'action_required')

    def test_forged_round_record_cannot_spend_or_exhaust_the_allowance(self):
        gh, app = test_spend.Spending().rounds(1)
        app.checks[1]['app']['id'] = 15368
        provider = Mock(return_value=report())
        _, app, errors, state = run_pipeline(self.docs(gh), app, provider=provider)
        self.assertEqual(errors, [])
        self.assertEqual(provider.call_count, 2)
        self.assertEqual(state['paid_rounds'], 1)


if __name__ == '__main__':
    unittest.main()
