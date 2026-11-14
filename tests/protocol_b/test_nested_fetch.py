"""Offline request-contract regression for PR98's nested web-fetch growth.

The fake provider models the documented response_inclusion behavior. These tests
do not claim to validate the live provider or run an independent review.
"""
import copy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from test_gate import FakeGH, gate, report


class NestedFetch(unittest.TestCase):
    def tearDown(self):
        gate.configure_budget([])

    def test_fetch_response_excludes_completed_nested_payloads_only(self):
        for profile in ('standard', 'expanded'):
            with self.subTest(profile=profile), patch.dict(os.environ, {'MANUSCRIPT_PROFILE': profile}):
                gate.configure_budget([{'filename': 'manuscripts/test.tex'}])
                messages = [{'role': 'user', 'content': 'Read the sources.'}]
                body = gate.model_body('fable', 'trusted', messages)
                fetch = next(t for t in body['tools'] if t['name'] == 'web_fetch')
                self.assertEqual(fetch.get('response_inclusion'), 'excluded')
                self.assertEqual(fetch['max_uses'], 20 if profile == 'expanded' else 5)
                self.assertEqual(fetch['max_content_tokens'], 50000 if profile == 'expanded' else 20000)
                self.assertEqual(body['max_tokens'], 64000)
                self.assertIs(body['messages'], messages)

    def test_nested_fetch_burst_returns_to_model_with_reads_and_history_intact(self):
        gh = FakeGH()
        reviewer = gate.Review(gh, gh.pr, [], [], {}, {}, 'trusted', 'fable', 'local mathematical')
        code_call = {'type': 'server_tool_use', 'id': 'code', 'name': 'code_execution',
                     'input': {'code': '# synthetic source-selection fixture'}}
        nested = []
        for index in range(12):
            ident = f'fetch{index}'
            binary = index < 3
            nested.extend([
                {'type': 'server_tool_use', 'id': ident, 'name': 'web_fetch',
                 'caller': {'type': 'code_execution_20260120', 'tool_id': 'code'},
                 'input': {'url': f'https://example.org/source-{index}'}},
                {'type': 'web_fetch_tool_result', 'tool_use_id': ident,
                 'content': {'type': 'web_fetch_result',
                             'content': {'type': 'document', 'source': {
                                 'type': 'base64' if binary else 'text',
                                 'data': 'x' * (250000 if binary else 100000)}}}}
            ])
        code_result = {'type': 'code_execution_tool_result', 'tool_use_id': 'code',
                       'content': {'type': 'code_execution_result', 'return_code': 0,
                                   'stdout': 'Selected source statements for checking.', 'stderr': '', 'content': []}}
        local_calls = [
            {'type': 'tool_use', 'id': 'read', 'name': 'read_file',
             'input': {'path': 'source.tex', 'revision': 'head', 'start': 1, 'count': 1}},
            {'type': 'tool_use', 'id': 'history', 'name': 'read_history', 'input': {}}
        ]
        observed = []
        def provider(family, instructions, conversation, **kwargs):
            observed.append(copy.deepcopy(conversation))
            if len(observed) == 1:
                fetch = next(t for t in gate.model_body(family, instructions, conversation)['tools']
                             if t['name'] == 'web_fetch')
                # Contract supplied by Anthropic, not client-side history editing:
                # completed code-consumed fetch pairs are omitted by the provider.
                retained = [] if fetch.get('response_inclusion') == 'excluded' else nested
                output = [code_call, *retained, code_result, *local_calls]
                usage = {'input_tokens': 161655, 'request_start_input_tokens': 161655,
                         'output_tokens': 1000, 'server_tool_use': {'web_fetch_requests': 12}}
            else:
                self.assertEqual(conversation[0], observed[0][0])
                self.assertEqual(conversation[-2]['content'], [code_call, code_result, *local_calls])
                results = [json.loads(x['content']) for x in conversation[-1]['content']]
                self.assertTrue(all('error' not in value for value in results))
                self.assertTrue(all(value['remaining_context_tokens'] > 0 for value in results))
                self.assertTrue(reviewer.history_read)
                self.assertEqual(reviewer.reads[-1]['path'], 'source.tex')
                output = [{'type': 'tool_use', 'id': 'finish', 'name': 'finish_review', 'input': report()}]
                usage = {'input_tokens': 162000, 'request_start_input_tokens': 162000, 'output_tokens': 100}
            return output, gate.MODELS[family], usage, 'offline-fixture', 'tool_use'

        with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
             patch.dict(os.environ, {'MANUSCRIPT_PROFILE': 'expanded', 'GITHUB_RUN_ID': 'fixture', 'GITHUB_RUN_ATTEMPT': '1'}), \
             patch.object(gh, 'text', return_value='A complete short source statement.'), \
             patch.object(gate, 'model_turn', side_effect=provider):
            gate.configure_budget([{'filename': 'manuscripts/test.tex'}])
            self.assertEqual(reviewer.run()['decision'], 'accept')
            budget = json.loads((Path(tmp)/'fable-context-budget.json').read_text())
            self.assertLess(budget['estimated_total'], 900000)
            trace = json.loads((Path(tmp)/'fable-web-results.json').read_text())
            self.assertEqual(trace[0]['unreturned_reported_fetches'], 12)
            self.assertEqual(trace[0]['next_request']['reported_input_tokens'], 162000)
            self.assertTrue(trace[0]['next_request']['assistant_replayed_unchanged'])
        self.assertEqual(len(observed), 2)

    def test_existing_direct_and_paused_history_is_not_filtered_by_client(self):
        content = [
            {'type': 'server_tool_use', 'id': 'direct', 'name': 'web_fetch', 'caller': None, 'input': {}},
            {'type': 'web_fetch_tool_result', 'tool_use_id': 'direct',
             'content': {'type': 'web_fetch_result', 'content': {'source': {'type': 'text', 'data': 'Direct source'}}}},
            {'type': 'server_tool_use', 'id': 'paused', 'name': 'web_fetch',
             'caller': {'type': 'code_execution_20260120', 'tool_id': 'unfinished-code'}, 'input': {}},
            {'type': 'web_fetch_tool_result', 'tool_use_id': 'paused',
             'content': {'type': 'web_fetch_result', 'content': {'source': {'type': 'text', 'data': 'Pending code input'}}}}
        ]
        messages = [{'role': 'assistant', 'content': content}]
        before = copy.deepcopy(messages)
        body = gate.model_body('fable', 'trusted', messages)
        gate.context_units('fable', body)
        self.assertEqual(body['messages'], before)
        self.assertEqual(messages, before)


if __name__ == '__main__':
    unittest.main()
