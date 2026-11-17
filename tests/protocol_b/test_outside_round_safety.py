"""Regressions for PR154's review history, pagination and per-PR serialization."""
import copy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import Mock, patch
from urllib.parse import parse_qs, urlsplit

import test_gate as tg
from test_gate import gate, HEAD, BASE, APP_ID
from test_outside_admission import Ledger, candidate
from test_outside_screen import NOW


class QuotaPagination(unittest.TestCase):
    def test_update_across_page_boundary_does_not_omit_reservation(self):
        class MovingLedger(Ledger):
            moved = False
            queries = []

            def pages(self, path):
                if path.startswith('/pulls?'):
                    return gate.GitHub.pages(self, path)
                return super().pages(path)

            def call(self, path):
                if not path.startswith('/pulls?'):
                    return super().call(path)
                query = parse_qs(urlsplit(path).query)
                self.queries.append(query)
                rows = sorted(self.pulls, key=lambda p: p['number'])
                if query['sort'] == ['updated'] and self.moved:
                    rows = rows[-1:] + rows[:-1]
                page = int(query['page'][0])
                result = copy.deepcopy(rows[(page-1)*100:page*100])
                if page == 1:
                    # A comment/close/reopen changes updated order, not creation order.
                    self.moved = True
                    self.pulls[-1]['updated_at'] = NOW.isoformat()
                return result

        ledger = MovingLedger()
        ledger.pulls = [{**copy.deepcopy(candidate()), 'number': n} for n in range(1, 102)]
        ledger.pr = ledger.pulls[-1]
        ledger.reserve()
        ledger.pr = ledger.pulls[19]
        with patch.object(gate, 'request') as provider:
            rows = ledger.read()
        self.assertEqual([r['pr'] for r in rows], [101])
        self.assertEqual([q['page'] for q in ledger.queries], [['1'], ['2']])
        self.assertTrue(all(q['sort'] == ['created'] and q['state'] == ['all'] for q in ledger.queries))
        provider.assert_not_called()

    def test_unstable_or_missing_pr_enumeration_fails_closed(self):
        for numbers in ([20, 20], [21, 20], [21], [0, 20]):
            with self.subTest(numbers=numbers), patch.object(gate, 'request') as provider:
                ledger = Ledger()
                ledger.pulls = [{**copy.deepcopy(candidate()), 'number': n} for n in numbers]
                with self.assertRaises(ValueError):
                    ledger.read()
                provider.assert_not_called()


class MergeHistory(unittest.TestCase):
    def fixture(self):
        gh = tg.Checks().ready_gh()
        gh.author_permission, gh.permission = 'read', 'write'
        gh.comments = [tg.comment('/protocol-b merge '+HEAD, user='maintainer')]
        reports = {f: tg.envelope(f) for f in gate.MODELS}
        digest = gate.passage_digest(sorted(gate.history_coverage(gate.history(gh, gh.pr)[0])))
        for report in reports.values():
            report['history_digest'] = digest
        value = {'schema': 'protocol-b-decisions/v1', 'number': 1, 'head': HEAD,
                 'policy_ref': BASE, 'reports': reports,
                 'review_round': {'number': 1, 'started': True, 'run': '1', 'attempt': '1', 'trigger': 'automatic'}}
        check = {'id': 202, 'name': gate.CHECK, 'head_sha': HEAD, 'app': {'id': APP_ID},
                 'status': 'completed', 'conclusion': 'success', 'output': {'text': json.dumps(value)}}
        gh.check_runs.append(check)
        return gh, check, value

    def execute(self, gh):
        with tempfile.TemporaryDirectory() as directory, \
                patch.dict(os.environ, {'GITHUB_SHA': BASE, 'APP_ID': str(APP_ID)}), \
                patch.object(gate, 'OUT', Path(directory)), \
                patch.object(gate, 'request') as provider:
            try:
                gate.outside_merge_command(gh, gh.pr, 'main', 'live')
            finally:
                provider.assert_not_called()

    def assert_no_merge(self, gh):
        self.assertEqual(gh.merge_requests, [])
        self.assertIsNone(gh.graphql)
        self.assertEqual(gh.dispatches, [])

    def test_unchanged_history_and_authorized_command_merge_without_models(self):
        gh, _, _ = self.fixture()
        self.execute(gh)
        self.assertEqual(len(gh.merge_requests), 1)
        self.assertEqual(len(gh.dispatches), 2)

    def test_unchanged_history_allows_deferred_merge_without_models(self):
        gh, _, _ = self.fixture()
        next(c for c in gh.check_runs if c['name'] != gate.CHECK)['status'] = 'in_progress'
        self.execute(gh)
        self.assertEqual(gh.merge_requests, [])
        self.assertIn('enablePullRequestAutoMerge', gh.graphql['query'])
        self.assertEqual(gh.dispatches, [])

    def test_new_objection_between_command_and_merge_readiness_still_blocks(self):
        gh, _, _ = self.fixture()
        original = gh.call
        def call(path, method='GET', data=None):
            if path == '/pulls/1':
                gh.comments.append(tg.comment('New objection after command validation.', user='visitor'))
            return original(path, method, data)
        gh.call = call
        with self.assertRaisesRegex(ValueError, 'history has changed'):
            self.execute(gh)
        self.assert_no_merge(gh)

    def test_new_objection_or_interrupted_review_blocks_old_acceptance(self):
        working = {'reviewer': 'fable', 'head': HEAD, 'run': '88', 'attempt': '1',
                   'notes': ['The new source does not establish this implication.']}
        observations = [tg.comment('This implication is false: consider zero.', user='visitor'),
                        tg.comment(gate.WORKING_MARKER+'\n```json\n'+json.dumps(working)+'\n```')]
        for observation in observations:
            for pending in (False, True):
                with self.subTest(body=observation['body'][:20], deferred=pending):
                    gh, _, _ = self.fixture()
                    observation['id'] = 44
                    gh.comments.append(observation)
                    if pending:
                        next(c for c in gh.check_runs if c['name'] != gate.CHECK)['status'] = 'in_progress'
                    with self.assertRaisesRegex(ValueError, 'history has changed'):
                        self.execute(gh)
                    self.assert_no_merge(gh)

    def test_later_acceptance_cannot_erase_an_undispositioned_prior_finding(self):
        gh, _, value = self.fixture()
        later = copy.deepcopy(value)
        later['reports']['fable'] = tg.envelope('fable', run='88', review=tg.report(
            decision='request_changes', findings=[{'id': 'F1', 'objection': 'Missing case', 'location': 'p:1'}]))
        # The successful check is newer, but its reports never dispositioned
        # this first round's finding. Serialization makes that history visible.
        gh.check_runs.append({'id': 201, 'name': gate.CHECK, 'head_sha': HEAD,
            'status': 'completed', 'conclusion': 'failure', 'app': {'id': APP_ID},
            'output': {'text': json.dumps(later)}})
        with self.assertRaisesRegex(ValueError, 'history has changed'):
            self.execute(gh)
        self.assert_no_merge(gh)

    def test_admin_scope_override_survives_only_with_unchanged_history_and_current_admin(self):
        for defect in (None, 'new_objection', 'write_only'):
            with self.subTest(defect=defect):
                gh, check, value = self.fixture()
                report = value['reports']['fable']
                report['review'] = tg.report(decision='request_changes', scope_complete=False,
                                             not_reviewed=['One source was unavailable.'])
                item = gate.review_scope_item(report)['id']
                gh.permission = 'admin'
                gh.comments.append(tg.comment('/protocol-b override '+HEAD+' '+item+' Accept explicit scope', user='maintainer'))
                discussion, _, overrides, _ = gate.history(gh, gh.pr, {item: {'objection': 'scope'}})
                value['overrides'] = gate.overridden_decision(value['reports'], overrides, HEAD)
                value['override_history_digest'] = gate.passage_digest(sorted(gate.history_coverage(discussion)))
                check['output']['text'] = json.dumps(value)
                if defect == 'new_objection':
                    gh.comments.append(tg.comment('A new mathematical gap.', user='visitor'))
                elif defect == 'write_only':
                    gh.permission = 'write'
                if defect:
                    with self.assertRaises(ValueError):
                        self.execute(gh)
                    self.assert_no_merge(gh)
                else:
                    self.execute(gh)
                    self.assertEqual(len(gh.merge_requests), 1)


class RoundSerialization(unittest.TestCase):
    def test_wake_does_not_route_while_an_explicit_command_is_running_or_pending(self):
        for status in ('queued', 'in_progress', 'requested', 'waiting', 'pending'):
            with self.subTest(status=status), patch.dict(os.environ, {'GITHUB_RUN_ID': '7'}), \
                    patch.object(gate, 'action_pages', side_effect=lambda gh, path, key: (
                        [{'id': 88, 'status': status}] if path.endswith('&status='+status) else [])), \
                    patch.object(gate, 'outside_app_id') as select_app, \
                    patch.object(gate, 'request') as provider:
                self.assertIsNone(gate.outside_wake_candidate(Mock(), 'main', {}))
                select_app.assert_not_called()
                provider.assert_not_called()

    def test_active_review_check_is_not_eligible_for_a_second_wake(self):
        check = {'id': 202, 'name': gate.CHECK, 'head_sha': HEAD,
                 'app': {'id': APP_ID}, 'status': 'in_progress',
                 'output': {'text': json.dumps({'schema': 'protocol-b-decisions/v1',
                                               'number': 20, 'head': HEAD})}}
        with patch.object(gate, 'head_checks', return_value=[check]), \
                patch.object(gate, 'request') as provider:
            self.assertFalse(gate.outside_retry_allowed(Mock(), candidate(), APP_ID, NOW))
            provider.assert_not_called()

    def test_all_routed_events_lock_review_and_publication_by_pr(self):
        job = tg.workflow.split('  run_reviewers:\n', 1)[1].split('  cleanup_kernel_refs:\n', 1)[0]
        lock = job.split('    concurrency:\n', 1)[1].split('    needs:', 1)[0]
        self.assertIn('group: protocol-b-review-pr-${{ needs.route_request.outputs.number }}', lock)
        self.assertIn('cancel-in-progress: false', lock)
        self.assertNotIn('github.run_id', lock)
        self.assertIn('review', job)
        self.assertIn('publish', job)
        # Both the PR event and the wake selector emit this same routing output.
        route = tg.source.split('def route_request():', 1)[1].split('def outside_existing_attempt', 1)[0]
        self.assertIn('pr = outside_wake_candidate', route)
        self.assertIn("number=str(pr['number'])", route)


if __name__ == '__main__':
    unittest.main()
