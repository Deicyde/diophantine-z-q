"""Offline regression tests for the actual program embedded in protocol-b.yml.

Run: python -B -m unittest discover -s tests/protocol_b -v
No credentials, network calls, model reviews, or GitHub writes are performed.
"""
import base64
import copy
import io
import json
import os
from pathlib import Path
import tempfile
import types
import unittest
from unittest.mock import patch
import urllib.error

ROOT = Path(__file__).resolve().parents[2]
workflow = (ROOT / '.github/workflows/protocol-b.yml').read_text(encoding='utf-8')
block = workflow.split("<<'PROTOCOL_B_PYTHON'\n", 1)[1].split('          PROTOCOL_B_PYTHON\n', 1)[0]
source = '\n'.join(line[10:] if line.startswith('          ') else line for line in block.splitlines()) + '\n'
gate = types.ModuleType('protocol_b_under_test')
exec(compile(source, '<embedded protocol-b program>', 'exec'), gate.__dict__)
HEAD, BASE, APP_ID = 'a' * 40, 'b' * 40, 123456


def changed(path='README.md', diff='@@ -1 +1 @@\n-alpha  \n+alpha', **kwargs):
    return {'filename': path, 'status': 'modified', 'patch': diff,
            'additions': 1, 'deletions': 1, **kwargs}


def report(**kwargs):
    return {'decision': 'accept', 'report': 'The source and its consumers have been read. The stated hypotheses match the supplied objects.',
            'findings': [], 'prior_findings': [], 'sources_read': ['test.tex:1'],
            'not_outside_reviewed': [], **kwargs}


def envelope(family='astra', **kwargs):
    return {'reviewer': family, 'model': gate.MODELS[family], 'head': HEAD, 'base': BASE,
            'run': '1', 'attempt': '1', 'complete': True, 'policy_ref': BASE,
            'review': report(), **kwargs}


def comment(body, user='github-actions[bot]'):
    return {'id': 3, 'user': {'login': user, 'type': 'Bot' if user.endswith('[bot]') else 'User'},
            'body': body, 'created_at': 'now', 'html_url': 'https://github.com/x/y/issues/1#issuecomment-3'}


def report_comment(value):
    return comment(gate.MARKER + '\n```json\n' + json.dumps(value) + '\n```')


class FakeGH:
    repo = 'x/y'

    def __init__(self):
        self.pr = {'number': 1, 'state': 'open', 'draft': False, 'head': {'sha': HEAD},
                   'base': {'sha': BASE, 'ref': 'main'}, 'changed_files': 1,
                   'title': 'Change', 'body': '', 'node_id': 'PR_1'}
        self.comments, self.posts, self.edits = [], [], []
        self.permission, self.graphql = 'read', None
        self.required = gate.REQUIRED_COMPUTATIONS | {gate.CHECK}
        self.integration, self.allow_auto_merge, self.strict = APP_ID, True, True
        self.main_sha, self.race, self.pr_calls = BASE, False, 0

    def pages(self, path):
        if path.endswith('/files'):
            return [changed('p.tex')]
        if '/issues/' in path:
            return self.comments
        return []

    def text(self, path, ref):
        return 'Review carefully. This is a test fixture, not a live provider call.'

    def call(self, path, method='GET', data=None):
        if path == '':
            return {'default_branch': 'main', 'allow_auto_merge': self.allow_auto_merge}
        if path.startswith('/commits/'):
            return {'sha': self.main_sha}
        if path == '/pulls/1':
            self.pr_calls += 1
            value = copy.deepcopy(self.pr)
            if self.race and self.pr_calls > 1:
                value['head']['sha'] = 'c' * 40
            return value
        if path.endswith('/permission'):
            return {'permission': self.permission}
        if path.endswith('/comments') and method == 'POST':
            self.posts.append(data)
            return {'id': len(self.posts) + 9}
        if path.startswith('/issues/comments/') and method == 'PATCH':
            self.edits.append(data)
            return {}
        if path.startswith('/rules/branches/'):
            return [{'type': 'required_status_checks', 'parameters': {
                'strict_required_status_checks_policy': self.strict,
                'required_status_checks': [{'context': n, 'integration_id': self.integration if n == gate.CHECK else 15368}
                                           for n in self.required]}}]
        raise AssertionError(('own-token unexpected operation', path, method))

    def api(self, path, method='GET', data=None):
        assert path == '/graphql'
        self.graphql = data
        return {'data': {}}


class FakeApp:
    def __init__(self):
        self.checks, self.created, self.final = {}, [], None

    def call(self, path, method='GET', data=None):
        if path == '/check-runs' and method == 'POST':
            value = {**copy.deepcopy(data), 'id': 20, 'app': {'id': APP_ID}}
            self.checks[20] = value
            self.created.append(copy.deepcopy(value))
            return value
        if path.startswith('/commits/') and '/check-runs?' in path:
            return {'check_runs': list(self.checks.values())}
        if path == '/check-runs/20':
            if method == 'GET':
                return self.checks[20]
            self.checks[20].update(copy.deepcopy(data))
            self.final = data
            return self.checks[20]
        raise AssertionError(('App-token unexpected operation', path, method))

    def prior(self, reports, app_id=APP_ID, ident=5):
        self.checks[ident] = {'id': ident, 'name': 'Protocol B / test review', 'head_sha': HEAD,
            'app': {'id': app_id}, 'output': {'text': json.dumps({
                'schema': 'protocol-b-decisions/v1', 'head': HEAD, 'reports': reports})}}


def run_pipeline(gh=None, app=None, mode='test', provider=None, event=None, finalize=True):
    gh, app = gh or FakeGH(), app or FakeApp()
    errors = []
    with tempfile.TemporaryDirectory() as tmp:
        temp = Path(tmp)
        event_path = temp / 'event.json'
        event_path.write_text(json.dumps(event or {'pull_request': {'number': 1}}))
        env = {'MODE': mode, 'TEST_PR': '1', 'GITHUB_EVENT_PATH': str(event_path),
               'GITHUB_REPOSITORY': 'x/y', 'GITHUB_REF': 'refs/heads/main', 'GITHUB_SHA': BASE,
               'GITHUB_RUN_ID': '7', 'GITHUB_RUN_ATTEMPT': '1', 'GITHUB_STEP_SUMMARY': str(temp / 'summary'),
               'GH_TOKEN': 'fake-gh', 'APP_TOKEN': 'fake-app', 'APP_ID': str(APP_ID),
               'OPENAI_API_KEY': 'fake-ai', 'ANTHROPIC_API_KEY': 'fake-anthropic'}
        def clients(repo, token):
            assert repo == 'x/y'
            return app if token == 'fake-app' else gh
        with patch.dict(os.environ, env), patch.object(gate, 'OUT', temp / 'out'), \
             patch.object(gate, 'GitHub', side_effect=clients), \
             patch.object(gate.Review, 'run', provider or (lambda self: report())):
            try:
                gate.main()
            except Exception as error:
                errors.append(str(error))
            if finalize:
                try:
                    gate.publish()
                except Exception as error:
                    errors.append(str(error))
            decision = temp / 'out/decision.json'
            state = json.loads(decision.read_text()) if decision.exists() else None
    return gh, app, errors, state


class Checks(unittest.TestCase):
    def test_actions_job_is_distinct_from_app_check(self):
        self.assertIn('  run_reviewers:\n    name: Run reviewers and publish App check\n', workflow)
        self.assertNotIn('\n  review:\n', workflow)
        self.assertEqual(gate.CHECK, 'Protocol B / review')

    def test_editorial_requires_declaration(self):
        self.assertEqual(gate.classify([changed()], True), 'editorial')
        self.assertNotEqual(gate.classify([changed()], False), 'editorial')

    def test_editorial_typos_and_credits(self):
        for path, diff in [('README.md', '-Welcom\n+Welcome'), ('CREDITS.md', '-Jenn Park\n+Jennifer Park')]:
            self.assertTrue((ROOT / path).is_file())
            self.assertEqual(gate.classify([changed(path, diff)], True), 'editorial')

    def test_editorial_math_and_sensitive_paths_rejected(self):
        for diff in ['-5\n+6', '-The claim is false\n+The claim is true', '-A theorem\n+A lemma']:
            self.assertNotEqual(gate.classify([changed(diff=diff)], True), 'editorial')
        for path in ['paper.tex', 'file.lean', 'checker.py', '.github/x.md', 'PROJECT.md', 'docs/research-review/README.md']:
            self.assertNotEqual(gate.classify([changed(path)], True), 'editorial')

    def test_truncated_diff_is_not_editorial(self):
        self.assertNotEqual(gate.classify([changed(additions=20)], True), 'editorial')

    def test_missing_patch_added_or_new_theorem_is_broad(self):
        missing = changed('p.pdf')
        missing.pop('patch')
        for value in [missing, changed(status='added'), changed(diff='-old\n+Theorem 4')]:
            self.assertEqual(gate.classify([value], True), 'new result or route')

    def test_prior_findings_cannot_be_omitted_or_duplicated(self):
        with self.assertRaisesRegex(ValueError, 'omitted'):
            gate.validate_review(report(), {'old'}, {})
        item = {'id': 'old', 'resolution': 'resolved', 'reason': 'fixed'}
        with self.assertRaisesRegex(ValueError, 'duplicated'):
            gate.validate_review(report(prior_findings=[item, item]), {'old'}, {})

    def test_acceptance_cannot_have_unresolved_findings(self):
        with self.assertRaisesRegex(ValueError, 'unresolved'):
            gate.validate_review(report(findings=[{'id': 'F1', 'location': 'p', 'objection': 'gap'}]), set(), {})

    def test_override_needs_authorization_and_disclosure(self):
        value = report(prior_findings=[{'id': 'F1', 'resolution': 'overridden', 'reason': 'owner decision'}])
        with self.assertRaisesRegex(ValueError, 'authenticated'):
            gate.validate_review(value, {'F1'}, {})
        with self.assertRaisesRegex(ValueError, 'outside reviewed'):
            gate.validate_review(value, {'F1'}, {'F1': {}})
        value['not_outside_reviewed'] = ['Claim H']
        gate.validate_review(value, {'F1'}, {'F1': {}})

    def test_history_keeps_findings_but_excludes_own_completed_prose(self):
        gh = FakeGH()
        value = envelope(review=report(report='x' * 45000, findings=[{'id': 'F1', 'location': 'p', 'objection': 'gap'}]))
        gh.comments = [report_comment({**value, 'run': str(i)}) for i in range(30)]
        discussion, prior, overrides, latest = gate.history(gh, gh.pr)
        self.assertEqual(discussion, [])
        self.assertEqual(len(prior), 30)
        self.assertFalse(overrides)

    def test_incomplete_observations_survive(self):
        gh = FakeGH()
        notes = {'run': '1', 'attempt': '1', 'reviewer': 'fable', 'notes': ['Possible gap H']}
        gh.comments = [comment(gate.WORKING_MARKER + '\n```json\n' + json.dumps(notes) + '\n```')]
        self.assertIn('Possible gap H', json.dumps(gate.history(gh, gh.pr)[0]))
        gh.comments.append(report_comment(envelope('fable')))
        self.assertEqual(gate.history(gh, gh.pr)[0], [])

    def test_override_permission_and_head_are_current(self):
        gh = FakeGH()
        gh.comments = [report_comment(envelope(review=report(findings=[{'id': 'F1'}]))),
                       comment('/protocol-b override ' + HEAD + ' 1-1-astra-F1 reason', 'collaborator')]
        self.assertFalse(gate.history(gh, gh.pr)[2])
        gh.permission = 'write'
        self.assertEqual(gate.history(gh, gh.pr)[2]['1-1-astra-F1']['collaborator'], 'collaborator')
        gh.comments[-1]['body'] = gh.comments[-1]['body'].replace(HEAD, BASE)
        self.assertFalse(gate.history(gh, gh.pr)[2])

    def test_full_ids_in_summary(self):
        summary = gate.findings_summary({'astra': envelope(review=report(findings=[{'id': 'F1', 'location': 'p:1', 'objection': 'gap'}]))})
        self.assertIn('1-1-astra-F1', summary)

    def test_override_incomplete_stale_or_uncovered_blocks(self):
        pair = {'astra': envelope(), 'fable': envelope('fable', review=report(decision='changes_requested', findings=[{'id': 'F1'}]))}
        with self.assertRaisesRegex(ValueError, 'Uncovered'):
            gate.overridden_decision(pair, {}, HEAD)
        for update in [{'complete': False}, {'head': BASE}, {'model': 'other'}]:
            invalid = copy.deepcopy(pair)
            invalid['fable'].update(update)
            with self.assertRaises(ValueError):
                gate.overridden_decision(invalid, {'1-1-fable-F1': {}}, HEAD)
        self.assertIn('1-1-fable-F1', gate.overridden_decision(pair, {'1-1-fable-F1': {}}, HEAD))

    def test_forged_actions_check_not_override_authority(self):
        app = FakeApp()
        pair = {'astra': envelope(), 'fable': envelope('fable')}
        app.prior(pair, app_id=15368)
        with patch.dict(os.environ, {'APP_ID': str(APP_ID)}):
            self.assertEqual(gate.trusted_reports(app, FakeGH().pr, 'Protocol B / test review', 20), {})
            app.prior(pair, ident=6)
            self.assertEqual(gate.trusted_reports(app, FakeGH().pr, 'Protocol B / test review', 20), pair)

    def test_override_uses_app_reports_without_model_calls(self):
        gh, app = FakeGH(), FakeApp()
        pair = {'astra': envelope(), 'fable': envelope('fable', review=report(decision='changes_requested', findings=[{'id': 'F1', 'location': 'p:1', 'objection': 'gap'}]))}
        app.prior(pair)
        gh.permission = 'write'
        command = comment('/protocol-b override ' + HEAD + ' 1-1-fable-F1 accepted limitation', 'collaborator')
        gh.comments = [report_comment(v) for v in pair.values()] + [command]
        event = {'issue': {'number': 1}, 'comment': command, 'sender': {'login': 'collaborator'}}
        with patch.object(gate, 'model_turn', side_effect=AssertionError('No model call permitted')):
            _, app, errors, _ = run_pipeline(gh, app, event=event,
                provider=lambda self: (_ for _ in ()).throw(AssertionError('No review permitted')))
        self.assertEqual(errors, [])
        self.assertEqual(app.final['conclusion'], 'success')
        self.assertIn('NOT outside reviewed', app.final['output']['summary'])

    def test_test_mode_never_merges_and_uses_distinct_tokens(self):
        gh, app, errors, _ = run_pipeline()
        self.assertEqual(errors, [])
        self.assertEqual(app.final['conclusion'], 'success')
        self.assertFalse(gh.graphql)
        self.assertEqual(app.created[0]['conclusion'], 'action_required')

    def test_unfinished_job_leaves_blocked_check(self):
        _, app, _, _ = run_pipeline(finalize=False)
        self.assertIsNone(app.final)
        self.assertEqual(app.checks[20]['conclusion'], 'action_required')

    def test_head_race_blocks(self):
        gh = FakeGH()
        gh.race = True
        gh, app, errors, _ = run_pipeline(gh)
        self.assertTrue(errors)
        self.assertEqual(app.final['conclusion'], 'failure')
        self.assertFalse(gh.graphql)

    def test_unrelated_base_advance_preserves_review(self):
        gh = FakeGH()
        gh.main_sha = 'c' * 40
        _, app, errors, _ = run_pipeline(gh)
        self.assertEqual(errors, [])
        self.assertEqual(app.final['conclusion'], 'success')

    def test_changed_trusted_policy_blocks_before_models(self):
        gh = FakeGH()
        gh.main_sha = 'c' * 40
        gh.text = lambda path, ref: ref
        _, app, errors, _ = run_pipeline(gh)
        self.assertTrue(errors)
        self.assertEqual(app.created, [])

    def test_live_requires_computation_checks_and_specific_app(self):
        for edit in ['missing', 'wrong_app', 'not_strict', 'auto_merge_off']:
            gh = FakeGH()
            if edit == 'missing': gh.required = {gate.CHECK}
            if edit == 'wrong_app': gh.integration = 15368
            if edit == 'not_strict': gh.strict = False
            if edit == 'auto_merge_off': gh.allow_auto_merge = False
            _, _, errors, _ = run_pipeline(gh, mode='live')
            self.assertTrue(errors, edit)
            self.assertFalse(gh.graphql, edit)

    def test_live_requests_only_guarded_auto_merge(self):
        gh, _, errors, _ = run_pipeline(mode='live')
        self.assertEqual(errors, [])
        self.assertIn('enablePullRequestAutoMerge', gh.graphql['query'])

    def test_transport_error_is_not_a_math_finding(self):
        def provider(review):
            if review.family == 'fable':
                raise RuntimeError('fixture API outage')
            return report()
        gh, app, errors, state = run_pipeline(provider=provider)
        self.assertTrue(errors)
        self.assertEqual(app.final['conclusion'], 'failure')
        self.assertFalse(state['reports']['fable']['complete'])
        self.assertEqual(state['reports']['fable']['review']['findings'], [])
        self.assertIn('fixture API outage', str(gh.posts))

    def test_disagreement_blocks(self):
        _, app, errors, _ = run_pipeline(provider=lambda r: report(decision='changes_requested' if r.family == 'fable' else 'accept'))
        self.assertTrue(errors)
        self.assertEqual(app.final['conclusion'], 'failure')

    def test_inactive_has_no_effects(self):
        with patch.dict(os.environ, {'MODE': 'off'}), patch.object(gate, 'GitHub') as ctor:
            gate.main()
            ctor.assert_not_called()

    def test_file_pages_download_once(self):
        gh = FakeGH()
        with patch.object(gh, 'text', return_value='one\ntwo\nthree') as fetch:
            review = gate.Review(gh, gh.pr, [], [], {}, {}, 'instructions', 'astra', 'local mathematical')
            for start in [1, 2, 3]:
                review.tool('read_file', {'path': 'a.tex', 'revision': 'head', 'start': start, 'count': 1})
            self.assertEqual(fetch.call_count, 1)

    def test_github_text_cache(self):
        gh = gate.GitHub('x/y', 'fake')
        value = {'type': 'file', 'size': 3, 'encoding': 'base64', 'content': base64.b64encode(b'abc').decode()}
        with patch.object(gh, 'call', return_value=value) as fetch:
            self.assertEqual(gh.text('x', HEAD), gh.text('x', HEAD))
            self.assertEqual(fetch.call_count, 1)


def stream(events):
    return io.BytesIO(''.join('data: ' + json.dumps(x) + '\n\n' for x in events).encode())


def anthropic_events(partial='', stop='tool_use'):
    return [
        {'type': 'message_start', 'message': {'id': 'm1', 'model': gate.MODELS['fable'], 'usage': {}}},
        {'type': 'content_block_start', 'index': 0, 'content_block': {'type': 'tool_use', 'id': 't1', 'name': 'read_history', 'input': {}}},
        {'type': 'content_block_delta', 'index': 0, 'delta': {'type': 'input_json_delta', 'partial_json': partial}},
        {'type': 'content_block_stop', 'index': 0},
        {'type': 'message_delta', 'delta': {'stop_reason': stop, 'stop_details': 'fixture detail'}, 'usage': {}},
        {'type': 'message_stop'}]


class Transport(unittest.TestCase):
    def test_added_file_read_at_base_returns_tool_error_then_head_succeeds(self):
        path = 'tests/fixtures/protocol-b-smoke.md'
        text = 'For rational x and y, 3*x^2 + 5*y^2 = 0 iff x = y = 0.'
        file_value = {'type': 'file', 'size': len(text), 'encoding': 'base64',
                      'content': base64.b64encode(text.encode()).decode()}
        for family in gate.MODELS:
            with self.subTest(family=family):
                gh = gate.GitHub('x/y', 'fake')
                pr = FakeGH().pr
                added = changed(path, status='added', diff='@@ -0,0 +1 @@\n+' + text, deletions=0)
                r = gate.Review(gh, pr, [added], [], {}, {}, 'instructions', family, 'new result or route')
                seen = []
                def call(name, args, ident):
                    if family == 'astra':
                        return {'type': 'function_call', 'name': name, 'arguments': json.dumps(args), 'call_id': ident}
                    return {'type': 'tool_use', 'name': name, 'input': args, 'id': ident}
                def model(actual_family, instructions, conversation):
                    seen.append(copy.deepcopy(conversation))
                    if len(seen) == 1:
                        output = [call('read_file', {'path': path, 'revision': 'base', 'start': 1, 'count': 10}, 'base')]
                    elif len(seen) == 2:
                        last = conversation[-1]
                        result = json.loads(last['output'] if family == 'astra' else last['content'][0]['content'])
                        self.assertIn(path, result['error'])
                        self.assertIn(BASE, result['error'])
                        self.assertIn('not found', result['error'])
                        self.assertEqual(r.reads, [])
                        self.assertNotIn((path, BASE), r.file_lines)
                        output = [call('read_file', {'path': path, 'revision': 'head', 'start': 1, 'count': 10}, 'head'),
                                  call('read_history', {}, 'history')]
                    else:
                        self.assertEqual(r.reads, [{'path': path, 'revision': HEAD, 'start': 1, 'count': 10}])
                        self.assertIn(text, json.dumps(conversation))
                        output = [call('finish_review', report(sources_read=[path + ':1']), 'finish')]
                    return output, gate.MODELS[actual_family], {}, 'fixture', 'completed' if family == 'astra' else 'tool_use'
                def urlopen(req, timeout):
                    prefix = 'https://api.github.com/repos/x/y/contents/' + path + '?ref='
                    if req.full_url == prefix + BASE:
                        raise urllib.error.HTTPError(req.full_url, 404, 'Not Found', {}, io.BytesIO(b'{"message":"Not Found"}'))
                    self.assertEqual(req.full_url, prefix + HEAD)
                    return io.BytesIO(json.dumps(file_value).encode())
                with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
                     patch.object(gate.urllib.request, 'urlopen', side_effect=urlopen) as fetch, \
                     patch.object(gate, 'model_turn', side_effect=model):
                    self.assertEqual(r.run()['decision'], 'accept')
                    self.assertEqual(fetch.call_count, 2)
                    saved = json.loads((Path(tmp) / (family + '-tool-0-0.json')).read_text())
                    self.assertIn('error', saved['result'])
                    self.assertEqual(saved['arguments']['revision'], 'base')
                self.assertEqual(len(seen), 3)

    def test_file_permission_server_and_blob_failures_remain_fatal(self):
        for status, blob in [(403, False), (500, False), (404, True)]:
            with self.subTest(status=status, blob=blob):
                gh = gate.GitHub('x/y', 'fake')
                r = gate.Review(gh, FakeGH().pr, [], [], {}, {}, 'instructions', 'fable', 'local mathematical')
                error = urllib.error.HTTPError('https://api.github.com/fixture', status, 'fixture', {}, io.BytesIO(b'failure'))
                responses = []
                if blob:
                    responses.append(io.BytesIO(json.dumps({'type': 'file', 'size': 2000000, 'encoding': 'none', 'sha': HEAD}).encode()))
                responses.append(error)
                with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
                     patch.object(gate.urllib.request, 'urlopen', side_effect=responses):
                    with self.assertRaises(gate.RequestError) as caught:
                        r.tool('read_file', {'path': 'paper.tex', 'revision': 'head', 'start': 1, 'count': 10})
                    self.assertEqual(caught.exception.status, status)
                    self.assertEqual(r.reads, [])

    def test_sse_multiline_and_done(self):
        self.assertEqual(list(gate.sse(io.BytesIO(b'data: {"type":\ndata: "ok"}\n\ndata: [DONE]\n\n'))), [{'type': 'ok'}])

    def test_empty_tool_delta_and_cache_and_budget(self):
        for delta in ['', '{}']:
            with patch.dict(os.environ, {'ANTHROPIC_API_KEY': 'fake'}), patch.object(gate, 'request', return_value=stream(anthropic_events(delta))) as req:
                output, model, usage, ident, stop = gate.model_turn('fable', 'trusted', [])
                self.assertEqual(output[0]['input'], {})
                self.assertEqual(stop, 'tool_use')
                self.assertEqual(req.call_args.args[3]['cache_control'], {'type': 'ephemeral', 'ttl': '1h'})
                self.assertEqual(req.call_args.args[3]['max_tokens'], 64000)

    def test_refusal_and_max_tokens_distinguishable(self):
        for reason in ['refusal', 'max_tokens']:
            with patch.dict(os.environ, {'ANTHROPIC_API_KEY': 'fake'}), patch.object(gate, 'request', return_value=stream(anthropic_events(stop=reason))):
                with self.assertRaisesRegex(RuntimeError, reason + '.*fixture detail'):
                    gate.model_turn('fable', 'trusted', [])

    def test_openai_completed_stream(self):
        event = {'type': 'response.completed', 'response': {'status': 'completed', 'id': 'r1', 'model': gate.MODELS['astra'], 'output': [], 'usage': {}}}
        with patch.dict(os.environ, {'OPENAI_API_KEY': 'fake'}), patch.object(gate, 'request', return_value=stream([event])) as req:
            self.assertEqual(gate.model_turn('astra', 'trusted', [])[1], gate.MODELS['astra'])
            self.assertEqual(req.call_args.args[3]['max_output_tokens'], 64000)

    def test_truncated_stream_blocks(self):
        with patch.dict(os.environ, {'OPENAI_API_KEY': 'fake'}), patch.object(gate, 'request', return_value=stream([])):
            with self.assertRaisesRegex(RuntimeError, 'without a completed'):
                gate.model_turn('astra', 'trusted', [])

    def test_model_mismatch_no_fallback(self):
        gh = FakeGH()
        r = gate.Review(gh, gh.pr, [], [], {}, {}, 'instructions', 'astra', 'local mathematical')
        with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
             patch.object(gate, 'model_turn', return_value=([], 'wrong-model', {}, 'x', 'completed')):
            with self.assertRaisesRegex(RuntimeError, 'no silent substitution'):
                r.run()

    def test_pause_turn_preserves_exact_assistant_without_user_message(self):
        gh = FakeGH()
        r = gate.Review(gh, gh.pr, [], [], {}, {}, 'instructions', 'fable', 'local mathematical')
        r.reads, r.history_read = [{'path': 'p'}], True
        paused = [{'type': 'text', 'text': 'Checking source.'}]
        seen = []
        def model(family, instructions, conversation):
            seen.append(copy.deepcopy(conversation))
            output = paused if len(seen) == 1 else [{'type': 'tool_use', 'id': 'f', 'name': 'finish_review', 'input': report()}]
            return output, gate.MODELS[family], {}, 'm', 'pause_turn' if len(seen) == 1 else 'tool_use'
        with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
             patch.dict(os.environ, {'GITHUB_RUN_ID': '1', 'GITHUB_RUN_ATTEMPT': '1'}), patch.object(gate, 'model_turn', model):
            r.run()
        self.assertEqual(seen[1][-1], {'role': 'assistant', 'content': paused})
        self.assertEqual(len(seen[1]), 2)

    def test_working_notes_update_one_comment(self):
        gh = FakeGH()
        r = gate.Review(gh, gh.pr, [], [], {}, {}, 'instructions', 'fable', 'local mathematical')
        r.reads, r.history_read = [{'path': 'p'}], True
        outputs = [[{'type': 'text', 'text': 'First observation'}], [{'type': 'text', 'text': 'Second observation'}],
                   [{'type': 'tool_use', 'id': 'f', 'name': 'finish_review', 'input': report()}]]
        with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
             patch.dict(os.environ, {'GITHUB_RUN_ID': '1', 'GITHUB_RUN_ATTEMPT': '1'}), \
             patch.object(gate, 'model_turn', side_effect=[(out, gate.MODELS['fable'], {}, 'm', 'end_turn') for out in outputs]):
            r.run()
        self.assertEqual(len(gh.posts), 1)
        self.assertEqual(len(gh.edits), 1)

    def test_only_initial_provider_429_or_5xx_retried(self):
        url = 'https://api.openai.com/v1/responses'
        def error(code):
            return urllib.error.HTTPError(url, code, 'fixture', {}, io.BytesIO(b'busy'))
        with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
             patch.object(gate.time, 'sleep') as sleep, \
             patch.object(gate.urllib.request, 'urlopen', side_effect=[error(429), error(503), io.BytesIO(b'')]) as open_url:
            gate.request(url, {}, 'POST', {}, True)
            self.assertEqual(open_url.call_count, 3)
            self.assertEqual(sleep.call_count, 2)
            self.assertEqual([c.args[0] for c in sleep.call_args_list], [65, 4])
        with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
             patch.object(gate.urllib.request, 'urlopen', side_effect=error(500)) as open_url:
            with self.assertRaises(RuntimeError):
                gate.request('https://api.github.com/repos/x/y/issues', {}, 'POST', {})
            self.assertEqual(open_url.call_count, 1)

    def test_rate_retry_obeys_header_and_bounded_wait(self):
        url = 'https://api.anthropic.com/v1/messages'
        for requested in [120, 900]:
            error = urllib.error.HTTPError(url, 429, 'fixture', {'Retry-After': str(requested)}, io.BytesIO(b'busy'))
            with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
                 patch.object(gate.time, 'sleep') as sleep, \
                 patch.object(gate.urllib.request, 'urlopen', side_effect=[error, io.BytesIO(b'')]) as open_url:
                if requested == 120:
                    gate.request(url, {}, 'POST', {}, True)
                    sleep.assert_called_once_with(120)
                    self.assertEqual(open_url.call_count, 2)
                else:
                    with self.assertRaisesRegex(RuntimeError, 'not retrying early'):
                        gate.request(url, {}, 'POST', {}, True)
                    sleep.assert_not_called()
                    self.assertEqual(open_url.call_count, 1)

    def test_spend_cap_is_not_retried_as_rate_limit(self):
        url = 'https://api.anthropic.com/v1/messages'
        payload = {'error': {'type': 'rate_limit_error', 'details': {'error_code': 'enforced_spend_limit_reached'}}}
        error = urllib.error.HTTPError(url, 429, 'fixture', {}, io.BytesIO(json.dumps(payload).encode()))
        with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
             patch.object(gate.time, 'sleep') as sleep, \
             patch.object(gate.urllib.request, 'urlopen', side_effect=error) as open_url:
            with self.assertRaisesRegex(RuntimeError, 'enforced_spend_limit_reached'):
                gate.request(url, {}, 'POST', {}, True)
            sleep.assert_not_called()
            self.assertEqual(open_url.call_count, 1)

    def test_context_budget_includes_cache_tokens_and_output_reserve(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)):
            first = gate.context_budget('fable', 'system', [])
            previous = {'request_bytes': first['request_bytes'], 'usage': {'input_tokens': 1000,
                        'cache_read_input_tokens': 200000, 'cache_creation_input_tokens': 50000, 'output_tokens': 1000}}
            second = gate.context_budget('fable', 'system', [], previous)
            self.assertEqual(second['estimated_total'], 252000 + 8192 + 64000)
            previous['usage']['cache_read_input_tokens'] = 300000
            with self.assertRaisesRegex(RuntimeError, 'context budget exceeded'):
                gate.context_budget('fable', 'system', [], previous)

    def test_context_budget_uses_complete_request_and_stops_before_api(self):
        gh = FakeGH()
        for family in gate.MODELS:
            r = gate.Review(gh, gh.pr, [], [], {}, {}, 'x' * 400000, family, 'local mathematical')
            with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
                 patch.object(gate, 'model_turn') as model:
                with self.assertRaisesRegex(RuntimeError, 'before the next model request'):
                    r.run()
                model.assert_not_called()
                self.assertEqual(len(r.instructions), 400000)

    def test_context_budget_counts_unicode_bytes_and_new_growth(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)):
            first = gate.context_budget('astra', 'system', [])
            prior = {'request_bytes': first['request_bytes'], 'usage': {'input_tokens': 300000, 'output_tokens': 0}}
            conversation = [{'role': 'user', 'content': '\U0001F50E' * 10000}]
            with self.assertRaisesRegex(RuntimeError, 'context budget exceeded'):
                gate.context_budget('astra', 'system', conversation, prior)
            self.assertEqual(len(conversation[0]['content']), 10000)

    def test_long_working_notes_continue_and_preserve_full_artifact(self):
        gh = FakeGH()
        r = gate.Review(gh, gh.pr, [], [], {}, {}, 'instructions', 'fable', 'local mathematical')
        r.reads, r.history_read = [{'path': 'p'}], True
        notes = [f'Observation {i}: ' + 'x' * 5000 for i in range(10)]
        outputs = [[{'type': 'text', 'text': note}] for note in notes]
        outputs.append([{'type': 'tool_use', 'id': 'f', 'name': 'finish_review', 'input': report()}])
        with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
             patch.dict(os.environ, {'GITHUB_RUN_ID': '1', 'GITHUB_RUN_ATTEMPT': '1'}), \
             patch.object(gate, 'model_turn', side_effect=[(out, gate.MODELS['fable'], {}, 'm', 'end_turn') for out in outputs]):
            self.assertEqual(r.run()['decision'], 'accept')
            saved = json.loads((Path(tmp) / 'fable-working-notes.json').read_text())
            self.assertEqual(saved['notes'], notes)
        self.assertEqual(len(gh.posts), 1)
        self.assertEqual(len(gh.edits), 9)
        final = gh.edits[-1]['body']
        self.assertLessEqual(len(final.encode('utf-8')), 45_000)
        self.assertIn(notes[-1], final)
        self.assertIn('Earlier notes are in the run artifact', final)

    def test_single_huge_unicode_note_fits_without_mutating_original(self):
        note = ('\U0001F50E\x00"\\' * 20_000) + 'LATEST TEXT'
        working = {'reviewer': 'fable', 'run': '1', 'attempt': '1', 'notes': [note],
                   'artifact_url': 'https://github.com/x/y/actions/runs/1/attempts/1'}
        rendered = gate.working_comment_body(working)
        self.assertLessEqual(len(rendered.encode('utf-8')), 45_000)
        self.assertIn('LATEST TEXT', rendered)
        self.assertIn('earlier_notes_in_artifact', rendered)
        self.assertEqual(working['notes'], [note])


if __name__ == '__main__':
    unittest.main(verbosity=2)
