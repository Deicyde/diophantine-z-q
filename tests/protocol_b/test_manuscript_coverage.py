"""Budget selection, committed PDF reads and narrow CI table attestations."""
import copy
import hashlib
import json
import os
from pathlib import Path
import subprocess
import socket
import tempfile
import time
import unittest
from unittest.mock import patch

from test_gate import gate, FakeGH, HEAD, BASE, changed, report, envelope


def tiny_pdf():
    """A real two-page, uncompressed PDF made only from this test's constants."""
    objs = [b'<< /Type /Catalog /Pages 2 0 R >>',
            b'<< /Type /Pages /Kids [3 0 R 5 0 R] /Count 2 >>',
            b'<< /Type /Page /Parent 2 0 R /MediaBox [0 0 200 200] /Resources << /Font << /F1 7 0 R >> >> /Contents 4 0 R >>',
            b'',
            b'<< /Type /Page /Parent 2 0 R /MediaBox [0 0 200 200] /Resources << /Font << /F1 7 0 R >> >> /Contents 6 0 R >>',
            b'', b'<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica >>']
    for i, word in [(3, 'first'), (5, 'second')]:
        stream = f'BT /F1 12 Tf 20 100 Td ({word} page) Tj ET'.encode()
        objs[i] = f'<< /Length {len(stream)} >>\nstream\n'.encode()+stream+b'\nendstream'
    result = b'%PDF-1.4\n'
    offsets = [0]
    for i, obj in enumerate(objs, 1):
        offsets.append(len(result))
        result += f'{i} 0 obj\n'.encode()+obj+b'\nendobj\n'
    xref = len(result)
    result += b'xref\n0 8\n0000000000 65535 f \n'
    result += b''.join(f'{offset:010} 00000 n \n'.encode() for offset in offsets[1:])
    return result+f'trailer\n<< /Size 8 /Root 1 0 R >>\nstartxref\n{xref}\n%%EOF\n'.encode()


class ManuscriptBudget(unittest.TestCase):
    def tearDown(self):
        gate.configure_budget([])

    def test_automatic_manuscript_and_data_budget_without_owner_variable(self):
        for path in ['manuscripts/q.tex', 'manuscripts/q.pdf', 'research/version20/tables/q.json',
                     'research/quartic214/table.txt', 'data/table.csv', 'docs/current-manuscript.json']:
            for var in ['', 'standard', 'expanded', 'old-unused-value']:
                with self.subTest(path=path, variable=var), patch.dict(os.environ, {'MANUSCRIPT_PROFILE': var}):
                    result = gate.configure_budget([changed(path)])
                    self.assertEqual(result['context_token_budget'], 900000)
                    self.assertEqual(result['tool_character_budget'], 2700000)
                    self.assertEqual(result['fable_web_max_uses'], {'web_search': 10, 'web_fetch': 20})
                    self.assertEqual(result['fable_web_fetch_max_content_tokens'], 50000)
                    self.assertEqual(result['output_token_budget'], 64000)

    def test_rename_out_and_delete_still_select_manuscript_budget(self):
        for file in [changed('old/q.txt', previous_filename='research/version20/q.txt', status='renamed'),
                     changed('manuscripts/q.tex', status='removed')]:
            self.assertEqual(gate.configure_budget([file])['context_token_budget'], 900000)
        for path in ['README.md', 'docs/readme.md', '.github/workflows/protocol-b.yml', 'ZInQKernel.lean']:
            self.assertEqual(gate.configure_budget([changed(path)])['context_token_budget'], 400000)


class PDFReads(unittest.TestCase):
    def test_both_reviewers_can_continue_from_committed_pdf_or_narrow_a_rejected_read(self):
        for family in gate.MODELS:
            for oversized in [False, True]:
                with self.subTest(family=family, oversized=oversized):
                    gh = FakeGH()
                    gh.blob = lambda *_: tiny_pdf()
                    reviewer = gate.Review(gh, gh.pr, [], [], {}, {}, 'trusted', family, 'local mathematical')
                    seen = []
                    def tool_call(name, args):
                        if family == 'fable':
                            return {'type': 'tool_use', 'id': str(len(seen))+name, 'name': name, 'input': args}
                        return {'type': 'function_call', 'call_id': str(len(seen))+name,
                                'name': name, 'arguments': json.dumps(args)}
                    def model(_family, _instructions, conversation, **kwargs):
                        seen.append(copy.deepcopy(conversation))
                        if len(seen) == 1:
                            output = [tool_call('read_pdf', {'path': 'paper.pdf', 'revision': 'head', 'start': 2, 'count': 1})]
                        elif len(seen) == 2:
                            received = json.dumps(conversation)
                            self.assertIn('Read too large' if oversized else 'second page', received)
                            if oversized:
                                self.assertEqual(reviewer.reads, [])
                            output = [tool_call('read_history', {})]
                            if oversized:
                                output.append(tool_call('read_file', {'path': 'p.tex', 'revision': 'head', 'start': 1, 'count': 1}))
                        else:
                            output = [tool_call('finish_review', report())]
                        return output, gate.MODELS[family], {}, 'fixture', 'tool_use'
                    with tempfile.TemporaryDirectory() as tmp, patch.object(gate, 'OUT', Path(tmp)), \
                         patch.object(gate, 'TOOL_CHARACTER_BUDGET', 5000), \
                         patch.object(gate, 'model_turn', side_effect=model), \
                         patch.object(gate, 'pdf_pages', return_value=[{'page': 2, 'text': 'x'*10000 if oversized else 'second page'}]):
                        self.assertEqual(reviewer.run()['decision'], 'accept')
                    self.assertEqual(len(seen), 3)

    def test_pinned_bytes_pages_hash_and_whole_file_dependency(self):
        for side, ref in [('head', HEAD), ('base', BASE)]:
            gh = FakeGH()
            gh.blob = lambda path, sha: tiny_pdf() if sha == ref else self.fail('wrong revision')
            reviewer = gate.Review(gh, gh.pr, [], [], {}, {}, 'trusted', 'fable', 'local mathematical')
            with patch.object(gate, 'pdf_pages', return_value=[{'page': 2, 'text': 'second page'}]):
                result = reviewer.tool('read_pdf', {'path': 'paper.pdf', 'revision': side, 'start': 2, 'count': 1})
            self.assertEqual(result['sha256'], hashlib.sha256(tiny_pdf()).hexdigest())
            self.assertEqual(result['revision'], ref)
            self.assertEqual(reviewer.reads[0]['start'], 2)
            self.assertIn(('paper.pdf', side), reviewer.binary_dependencies)
            binding = gate.make_reuse_binding(gh, gh.pr, [], reviewer)
            self.assertIn('paper.pdf', {x['path'] for x in binding['sources']})

    def test_invalid_ranges_and_failed_extraction_never_count_as_a_read(self):
        for start, count in [(0, 1), (1, 11), (True, 1)]:
            with self.assertRaises(ValueError):
                gate.pdf_pages(tiny_pdf(), start, count)
        gh = FakeGH()
        gh.blob = lambda *_: b'not a pdf'
        reviewer = gate.Review(gh, gh.pr, [], [], {}, {}, 'trusted', 'astra', 'local mathematical')
        with self.assertRaises(ValueError):
            reviewer.tool('read_pdf', {'path': 'paper.pdf', 'revision': 'head', 'start': 1, 'count': 1})
        self.assertEqual(reviewer.reads, [])

    def test_isolation_timeout_no_secret_env_and_no_fallback(self):
        command = gate.pdf_command(Path('/input'), Path('/output'), 2, 3)
        for flag in ['--unshare-all', '--clearenv', '--cap-drop', '--die-with-parent', '--as=536870912']:
            self.assertIn(flag, command)
        self.assertNotIn('--share-net', command)
        self.assertNotIn('/proc', command)
        self.assertEqual(command[:6], ['/usr/bin/sudo', '-n', '/usr/bin/timeout', '--signal=KILL', '35', '/usr/bin/bwrap'])
        self.assertIn('/output.txt', command)
        with patch.dict(os.environ, {'ANTHROPIC_API_KEY': 'must-not-inherit'}), \
             patch.object(gate.subprocess, 'run', side_effect=subprocess.TimeoutExpired(command, 35)) as run:
            with self.assertRaisesRegex(ValueError, 'timed out'):
                gate.pdf_pages(tiny_pdf(), 1, 1)
            self.assertNotIn('ANTHROPIC_API_KEY', run.call_args.kwargs['env'])
            self.assertNotIn('timeout', run.call_args.kwargs)  # Privileged timeout kills the process group.
            self.assertEqual(run.call_count, 1)

    @unittest.skipUnless(os.environ.get('PROTOCOL_B_TEST_PDF_ISOLATION') == '1',
                         'Real isolated reader runs in the dedicated secret-free Linux job')
    def test_actual_poppler_in_isolation(self):
        pages = gate.pdf_pages(tiny_pdf(), 2, 1)
        self.assertEqual(len(pages), 1)
        self.assertEqual(pages[0]['page'], 2)
        self.assertIn('second page', pages[0]['text'])
        self.assertNotIn('first page', pages[0]['text'])

    @unittest.skipUnless(os.environ.get('PROTOCOL_B_TEST_PDF_ISOLATION') == '1', 'Linux isolation probe')
    def test_actual_isolation_environment_files_network_and_timeout(self):
        original = gate.pdf_command
        def command_for(program, seconds='35'):
            def build(source, output, start, count):
                cmd = original(source, output, start, count)
                cmd[4] = seconds
                return cmd[:cmd.index('/usr/bin/pdftotext')]+program
            return build
        with socket.socket() as listener:
            listener.bind(('127.0.0.1', 0))
            listener.listen()
            port = listener.getsockname()[1]
            code = f'''import os,pathlib,socket
# bubblewrap sets PWD itself after applying --clearenv and --chdir.
assert dict(os.environ) == {{'PATH': '/usr/bin', 'LC_ALL': 'C.UTF-8', 'PWD': '/'}}, sorted(os.environ)
assert not pathlib.Path('/home').exists() and not pathlib.Path('/proc').exists()
assert not pathlib.Path('/etc').exists()
assert pathlib.Path('/input.pdf').read_bytes().startswith(b'%PDF-')
s=socket.socket(); s.settimeout(1)
assert s.connect_ex(('127.0.0.1',{port})) != 0
pathlib.Path('/output.txt').write_text('isolation passed\\f')
'''
            with patch.object(gate, 'pdf_command', side_effect=command_for(['/usr/bin/python3', '-c', code])), \
                 patch.dict(os.environ, {'ANTHROPIC_API_KEY': 'test-sentinel-not-a-key'}):
                self.assertIn('isolation passed', gate.pdf_pages(tiny_pdf(), 1, 1)[0]['text'])
        began = time.monotonic()
        with patch.object(gate, 'pdf_command', side_effect=command_for(['/usr/bin/sleep', '120'], '1')):
            with self.assertRaisesRegex(ValueError, 'extraction failed'):
                gate.pdf_pages(tiny_pdf(), 1, 1)
        self.assertLess(time.monotonic()-began, 10)
        def missing(source, output, start, count):
            cmd = original(source, output, start, count)
            cmd[5] = '/no-such-bwrap'
            return cmd
        with patch.object(gate, 'pdf_command', side_effect=missing) as wrapper:
            with self.assertRaisesRegex(ValueError, 'extraction failed'):
                gate.pdf_pages(tiny_pdf(), 1, 1)
            self.assertEqual(wrapper.call_count, 1)

    @unittest.skipUnless(os.environ.get('PROTOCOL_B_TEST_PDF_ISOLATION') == '1', 'Linux large-PDF probe')
    def test_late_page_of_committed_manuscript(self):
        root = Path(__file__).resolve().parents[2]
        # V19 is released and immutable. Its late mathematical pages exercise
        # the actual Poppler memory/CPU limits against the committed large PDF.
        path = root/'manuscripts/quartic_v19.pdf'
        pages = gate.pdf_pages(path.read_bytes(), 700, 1)
        self.assertEqual(len(pages), 1)
        self.assertEqual(pages[0]['page'], 700)
        self.assertTrue(pages[0]['text'].strip())


class CITableCoverage(unittest.TestCase):
    def setUp(self):
        self.gh = FakeGH()
        self.job = {'status': 'completed', 'conclusion': 'success', 'run_id': 22, 'run_attempt': 1,
                    'head_sha': HEAD, 'name': 'Finite tables', 'html_url': 'https://github.com/x/y/actions/runs/22/job/11',
                    'steps': [{'number': 2, 'name': 'Check printed table', 'status': 'completed', 'conclusion': 'success'}]}
        self.run = {'id': 22, 'run_attempt': 1, 'head_sha': HEAD, 'event': 'push',
                    'repository': {'full_name': 'x/y'}, 'head_repository': {'full_name': 'x/y'},
                    'path': '.github/workflows/finite.yml'}
        self.parents = [BASE, HEAD]
        original = self.gh.call
        def call(path, *a, **kw):
            if path == '/actions/jobs/11': return copy.deepcopy(self.job)
            if path in ['/actions/runs/22/attempts/1', '/actions/runs/22']: return copy.deepcopy(self.run)
            if path.startswith('/commits/'): return {'parents': [{'sha': p} for p in self.parents]}
            return original(path, *a, **kw)
        self.gh.call = call
        self.reviewer = gate.Review(self.gh, self.gh.pr, [], [], {}, {}, 'trusted', 'astra', 'local mathematical')
        self.args = {'job_id': 11, 'step_number': 2, 'table_path': 'manuscripts/q.tex', 'table_location': 'Table 1',
                     'checker_paths': ['scripts/check.py'], 'data_paths': ['research/version20/table.json'],
                     'claim_and_limits': 'Step 2 runs check.py on the committed JSON and parses every printed table entry in q.tex; exact finite equality only, not the soundness theorem.'}

    def read(self):
        for path in ['.github/workflows/finite.yml', 'scripts/check.py', 'manuscripts/q.tex']:
            self.reviewer.tool('read_file', {'path': path, 'revision': 'head', 'start': 1, 'count': 1000})
        self.reviewer.tool('read_ci_job', {'job_id': 11})

    def test_records_exact_ci_step_and_committed_data(self):
        self.read()
        result = self.reviewer.tool('record_table_coverage', self.args)
        self.assertEqual(result['table_coverage']['reviewed_head'], HEAD)
        self.assertIn('research/version20/table.json', result['table_coverage']['blobs'])
        self.assertEqual(self.reviewer.table_coverage, [result['table_coverage']])
        with self.assertRaisesRegex(ValueError, 'fresh CI inspection'):
            gate.make_reuse_binding(self.gh, self.gh.pr, [], self.reviewer)

    def test_stale_or_failed_or_skipped_ci_is_not_coverage(self):
        for status in ['failure', 'skipped', 'cancelled', 'neutral']:
            self.job['conclusion'] = status
            with self.assertRaisesRegex(ValueError, 'successfully'):
                gate.ci_job_evidence(self.gh, self.gh.pr, 11)
        self.job['conclusion'] = 'success'
        self.job['head_sha'] = self.run['head_sha'] = 'c'*40
        self.parents = ['d'*40, HEAD]
        with self.assertRaisesRegex(ValueError, 'exact head'):
            gate.ci_job_evidence(self.gh, self.gh.pr, 11)
        self.parents = [BASE, HEAD]
        with self.assertRaisesRegex(ValueError, 'exact head'):
            gate.ci_job_evidence(self.gh, self.gh.pr, 11)
        self.job['head_sha'] = self.run['head_sha'] = HEAD
        self.read()
        self.job['steps'][0]['conclusion'] = 'skipped'
        self.reviewer.tool('read_ci_job', {'job_id': 11})
        with self.assertRaisesRegex(ValueError, 'successful step'):
            self.reviewer.tool('record_table_coverage', self.args)

    def test_unread_checker_and_changed_data_are_refused(self):
        self.reviewer.tool('read_ci_job', {'job_id': 11})
        with self.assertRaisesRegex(ValueError, 'complete workflow'):
            self.reviewer.tool('record_table_coverage', self.args)
        self.read()
        self.reviewer.reads = [r for r in self.reviewer.reads if r['path'] != 'scripts/check.py']
        with self.assertRaisesRegex(ValueError, 'complete workflow'):
            self.reviewer.tool('record_table_coverage', self.args)
        self.read()
        with patch.object(gate, 'source_identity', side_effect=['d'*40, 'e'*40]):
            with self.assertRaisesRegex(ValueError, 'different committed bytes'):
                self.reviewer.tool('record_table_coverage', self.args)
        self.assertEqual(self.reviewer.table_coverage, [])

    def test_refuses_test_merge_behind_base_and_foreign_pr_at_same_head(self):
        for event in ['pull_request', 'pull_request_target', 'schedule', 'invented']:
            for parents in [[BASE, HEAD], ['c'*40, HEAD]]:
                self.run['event'] = event
                self.parents = parents
                self.run['pull_requests'] = [{'number': 999, 'base': {'sha': parents[0]}, 'head': {'sha': HEAD}}]
                with self.subTest(event=event, parents=parents), self.assertRaisesRegex(ValueError, 'test-merge and fork'):
                    gate.ci_job_evidence(self.gh, self.gh.pr, 11)
        self.run['event'] = 'workflow_dispatch'
        self.assertEqual(gate.ci_job_evidence(self.gh, self.gh.pr, 11)['event'], 'workflow_dispatch')
        for field in ['repository', 'head_repository']:
            original = self.run[field]
            self.run[field] = {'full_name': 'foreign/fork'}
            with self.assertRaisesRegex(ValueError, 'test-merge and fork'):
                gate.ci_job_evidence(self.gh, self.gh.pr, 11)
            self.run[field] = original
        self.run['run_attempt'] = 2
        with self.assertRaisesRegex(ValueError, 'older attempt'):
            gate.ci_job_evidence(self.gh, self.gh.pr, 11)

    def test_bad_tool_arguments_and_api_errors_are_recoverable(self):
        self.read()
        for name, args in [('record_table_coverage', {**self.args, 'checker_paths': None}),
                           ('read_ci_job', {}), ('list_ci_checks', {}),
                           ('read_pdf', {'path': None, 'revision': 'head'})]:
            with self.subTest(name=name), self.assertRaises(ValueError):
                self.reviewer.tool(name, args)
        for error in [OSError('disk'), TypeError('bad field'), KeyError('absent'), gate.RequestError({'status': 404, 'body': 'not found'})]:
            with patch.object(gate, 'source_identity', side_effect=error):
                with self.assertRaisesRegex(ValueError, 'could not return evidence'):
                    self.reviewer.tool('record_table_coverage', self.args)
            self.assertEqual(self.reviewer.table_coverage, [])

    def test_many_full_claims_do_not_overflow_compact_app_record(self):
        self.read()
        claim = self.reviewer.tool('record_table_coverage', self.args)['table_coverage']
        claim['claim_and_limits'] += 'detailed finite claim '*1000
        claim['steps'] += [{'number': i, 'name': 'Other step '+str(i)+'x'*200,
                           'status': 'completed', 'conclusion': 'success'} for i in range(3, 100)]
        reports = {family: envelope(family, ci_table_coverage=[copy.deepcopy(claim) for _ in range(12)])
                   for family in gate.MODELS}
        original = copy.deepcopy(reports)
        state = {'head': HEAD, 'reports': reports}
        text = gate.decision_text(state, reports, [])
        self.assertLess(len(text.encode()), 30000)
        saved = json.loads(text)['reports']['astra']['ci_table_coverage']
        self.assertEqual(saved['count'], 12)
        self.assertNotIn('steps', saved['claims'][0])
        self.assertIn('blobs', saved['claims'][0])
        self.assertEqual(reports, original)
        self.assertTrue(gate.bounded_decision(state, reports, {}, [])[0])

    def test_tool_failures_do_not_end_either_provider_review(self):
        for family in gate.MODELS:
            for failure in [OSError('read unavailable'), TypeError('malformed API'), KeyError('field'), gate.RequestError({'status': 404, 'body': 'not found'})]:
                gh = FakeGH()
                original = gh.call
                failed = [False]
                def call(path, *args, **kwargs):
                    if '/check-runs' in path and len(turns) == 1 and not failed[0]:
                        failed[0] = True
                        raise failure
                    return original(path, *args, **kwargs)
                gh.call = call
                reviewer = gate.Review(gh, gh.pr, [], [], {}, {}, 'trusted', family, 'local mathematical')
                turns = []
                def tool(name, arguments):
                    if family == 'fable':
                        return {'type': 'tool_use', 'id': name+str(len(turns)), 'name': name, 'input': arguments}
                    return {'type': 'function_call', 'call_id': name+str(len(turns)),
                            'name': name, 'arguments': json.dumps(arguments)}
                def model(_family, _instructions, conversation, **kwargs):
                    turns.append(copy.deepcopy(conversation))
                    if len(turns) == 1:
                        output = [tool('list_ci_checks', {'offset': 0})]
                    elif len(turns) == 2:
                        self.assertIn('could not return evidence', json.dumps(conversation))
                        output = [tool('read_file', {'path': 'p.tex', 'revision': 'head', 'start': 1, 'count': 1}),
                                  tool('read_history', {})]
                    else:
                        output = [tool('finish_review', report())]
                    return output, gate.MODELS[family], {}, 'fixture', 'tool_use'
                with self.subTest(family=family, failure=type(failure).__name__), tempfile.TemporaryDirectory() as tmp, \
                     patch.object(gate, 'OUT', Path(tmp)), patch.object(gate, 'model_turn', side_effect=model):
                    self.assertEqual(reviewer.run()['decision'], 'accept')
                    self.assertEqual(len(turns), 3)

    def test_ci_never_makes_incomplete_scope_or_a_gap_accept(self):
        self.read()
        self.reviewer.tool('record_table_coverage', self.args)
        with self.assertRaisesRegex(ValueError, 'Incomplete review cannot accept'):
            gate.validate_review(report(scope_complete=False, not_reviewed=['Proof argument']), set(), {})
        value = report(decision='changes_requested', findings=[{'id': 'GAP', 'location': 'proof',
            'kind': 'gap', 'objection': 'Missing proof of completeness', 'attempted_resolution': 'Checked the adjoining lemma; it only proves necessity.'}])
        self.assertEqual(gate.validate_review(value, set(), {})['decision'], 'changes_requested')


if __name__ == '__main__':
    unittest.main()
