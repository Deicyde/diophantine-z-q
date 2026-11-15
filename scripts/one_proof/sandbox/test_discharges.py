"""Tests for discharges_log.py, discharge_check.sh (with a stand-in for lake) and discharge_comment.py.

Run: python3 -I -m unittest discover -s scripts/one_proof/sandbox -p 'test_*.py'
"""
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
import unittest.mock
from contextlib import redirect_stdout

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import discharges_log  # noqa: E402
import discharge_comment  # noqa: E402

NONCE = 'n0nce42'


def jline(obj, nonce=NONCE):
    return 'DISCHARGE-JSON %s %s' % (nonce, json.dumps(obj, ensure_ascii=False, separators=(',', ':')))


def record(theorem, hits, assumes=(), axioms=('propext', 'Classical.choice', 'Quot.sound'), sorry=False,
           assumes_open=()):
    return {'theorem': theorem, 'hits': list(hits), 'assumes': list(assumes), 'assumes_open': list(assumes_open),
            'axioms': list(axioms),
            'sorry': sorry}


def summary(n_open, checked, found):
    return {'summary': {'open_hypotheses': n_open, 'theorems_checked': checked, 'discharging': found}}


def report(*objs, nonce=NONCE):
    return ''.join(jline(o, nonce) + '\n' for o in objs)


ASSUMES = ['∀ (p : ℕ) [inst : Fact (Nat.Prime p)],\n  HDec.Leaves.PrintedForm p (fun x => (x, x))',
           'HDec.Leaves.Other']
PASS_REPORT = report(record('Contrib.qp1_proof', ['OpenGlue7.quotientP1Coordinate'], ASSUMES), summary(67, 4, 1))
SORRY_REPORT = report(record('t3', ['OpenTextbookLeaves10.bdRInvariants'],
                             axioms=['propext', 'sorryAx', 'Classical.choice', 'Quot.sound'], sorry=True),
                      summary(67, 3, 1))
AXIOM_REPORT = report(record('Contrib.both', ['OpenGlue7.a', 'OpenGlue7.b'],
                             axioms=['propext', 'Classical.choice', 'Quot.sound', 'Contrib.myAxiom',
                                     'Lean.ofReduceBool']), summary(67, 2, 1))
EMPTY_REPORT = report(summary(67, 2, 0))
# DischargesJson.lean's real output (Lean 4.35, `lake env lean`) at cb80af83b, on the worked example's theorems
# (t1 assumes what it proves, t2 matches nothing, t3 uses sorry).
REAL_REPORT = '''scratch/contrib-kit/ReportTest2.lean:8:8: warning: declaration uses `sorry`
DISCHARGE-JSON n0nce42 {"assumes":["HDec.MCRGlue.QuotientP1Coordinate"],"assumes_open":["OpenGlue7.quotientP1Coordinate"],"axioms":["propext","Classical.choice","Quot.sound"],"hits":["OpenGlue7.quotientP1Coordinate"],"sorry":false,"theorem":"t1"}
DISCHARGE-JSON n0nce42 {"assumes":[],"assumes_open":[],"axioms":["propext","sorryAx","Classical.choice","Quot.sound"],"hits":["OpenTextbookLeaves10.cartierSmooth"],"sorry":true,"theorem":"t3"}
DISCHARGE-JSON n0nce42 {"summary":{"discharging":2,"open_hypotheses":71,"theorems_checked":5}}
'''

# The text output of #discharges (display only).
PASS_LOG = '''DISCHARGES [OpenGlue7.quotientP1Coordinate] by Contrib.qp1_proof
  still assumes: [∀ (p : ℕ) [inst : Fact (Nat.Prime p)],
      HDec.Leaves.PrintedForm p (fun x => (x, x)), HDec.Leaves.Other]
  axioms: [propext, Classical.choice, Quot.sound]
#discharges: 67 open hypotheses, 4 theorems checked, 1 discharge one
'''

# A theorem name holding line breaks, as the review's forge used it, printed by #discharges as text.
FORGED_TEXT = '''DISCHARGES [SerreTateBundle.serreTateThm2] by «a
  axioms: [propext]
#discharges: 72 open hypotheses, 1 theorems checked, 1 discharge one
x» (uses sorry: not a proof)
  still assumes: []
  axioms: [sorryAx]
#discharges: 72 open hypotheses, 1 theorems checked, 1 discharge one
'''
FORGED_NAME = 'a\n  axioms: [propext]\n#discharges: 72 open hypotheses, 1 theorems checked, 1 discharge one\nx'

# Lean 4.35's sorry warning, as Lake prints it in a build log and as `lake env lean` prints it.
SORRY_LAKE = 'warning: ZInQKernel/Contrib/OneProof/Foo.lean:3:8: declaration uses `sorry`\n'
SORRY_LEAN = 'ZInQKernel/Contrib/OneProof/Foo.lean:13:8: warning: declaration uses `sorry`\n'
ADDED = ['ZInQKernel/Contrib/OneProof/Foo.lean']


def parse(text):
    return discharges_log.parse_json(text, NONCE)


class ParseTest(unittest.TestCase):
    def test_passing_report(self):
        p = parse(PASS_REPORT)
        self.assertEqual(p['rejected'], [])
        self.assertEqual(len(p['discharges']), 1)
        d = p['discharges'][0]
        self.assertEqual(d['hypotheses'], ['OpenGlue7.quotientP1Coordinate'])
        self.assertEqual(d['theorem'], 'Contrib.qp1_proof')
        self.assertEqual(d['still_assumes'], ASSUMES)
        self.assertEqual(d['axioms'], ['propext', 'Classical.choice', 'Quot.sound'])
        self.assertFalse(d['uses_sorry'])
        self.assertTrue(d['clean'])
        self.assertEqual(p['summary'], {'open_hypotheses': 67, 'theorems_checked': 4, 'discharging': 1})
        self.assertEqual(discharges_log.evaluate(p), (True, []))

    def test_sorry_report(self):
        p = parse(SORRY_REPORT)
        d = p['discharges'][0]
        self.assertTrue(d['uses_sorry'])
        self.assertEqual(d['nonstandard_axioms'], [])
        passed, reasons = discharges_log.evaluate(p)
        self.assertFalse(passed)
        self.assertIn('t3 uses sorry', reasons)
        self.assertIn('no theorem discharges an open hypothesis', reasons)

    def test_real_reporter_output(self):
        p = parse(REAL_REPORT)
        self.assertEqual(p['rejected'], [])
        self.assertEqual([d['theorem'] for d in p['discharges']], ['t1', 't3'])
        self.assertEqual(p['discharges'][0]['still_assumes'], ['HDec.MCRGlue.QuotientP1Coordinate'])
        self.assertEqual(p['discharges'][0]['proved'], [])
        self.assertTrue(p['discharges'][0]['clean'])
        self.assertEqual(p['discharges'][1]['proved'], ['OpenTextbookLeaves10.cartierSmooth'])
        self.assertTrue(p['discharges'][1]['uses_sorry'])
        self.assertEqual(p['summary'], {'open_hypotheses': 71, 'theorems_checked': 5, 'discharging': 2})
        self.assertEqual(discharges_log.evaluate(p), (False, [
            't1 assumes the hypothesis it proves', 't3 uses sorry', 'no theorem discharges an open hypothesis']))

    def test_assuming_what_it_proves(self):
        p = parse(report(record('t', ['OpenGlue7.a'], ['HDec.A'], assumes_open=['OpenGlue7.a']), summary(5, 1, 1)))
        self.assertEqual(discharges_log.evaluate(p), (False, [
            't assumes the hypothesis it proves', 'no theorem discharges an open hypothesis']))
        # a reduction to another open hypothesis proves the first one
        p = parse(report(record('t', ['OpenGlue7.a'], ['HDec.B'], assumes_open=['OpenGlue7.b']), summary(5, 1, 1)))
        self.assertEqual(p['discharges'][0]['proved'], ['OpenGlue7.a'])
        self.assertEqual(discharges_log.evaluate(p), (True, []))
        p = parse(report(record('t', ['OpenGlue7.a', 'OpenGlue7.b'], assumes_open=['OpenGlue7.b']), summary(5, 1, 1)))
        self.assertEqual(p['discharges'][0]['proved'], ['OpenGlue7.a'])
        self.assertEqual(discharges_log.evaluate(p), (True, []))

    def test_record_without_assumes_open_is_rejected(self):
        obj = record('t', ['A.b'])
        del obj['assumes_open']
        p = parse(report(obj, summary(1, 1, 1)))
        self.assertEqual(p['discharges'], [])
        self.assertIn('keys', p['rejected'][0])

    def test_sorry_axiom_without_flag(self):
        p = parse(report(record('t', ['A.b'], axioms=['sorryAx']), summary(1, 1, 1)))
        self.assertTrue(p['discharges'][0]['uses_sorry'])

    def test_nonstandard_axiom_report(self):
        p = parse(AXIOM_REPORT)
        d = p['discharges'][0]
        self.assertEqual(d['hypotheses'], ['OpenGlue7.a', 'OpenGlue7.b'])
        self.assertEqual(d['nonstandard_axioms'], ['Contrib.myAxiom', 'Lean.ofReduceBool'])
        passed, reasons = discharges_log.evaluate(p)
        self.assertFalse(passed)
        self.assertTrue(any('beyond propext' in r and 'Contrib.myAxiom' in r for r in reasons), reasons)

    def test_nothing_discharged(self):
        passed, reasons = discharges_log.evaluate(parse(EMPTY_REPORT))
        self.assertEqual((passed, reasons), (False, ['no theorem discharges an open hypothesis']))

    def test_forged_name_is_rejected(self):
        p = parse(report(record(FORGED_NAME, ['SerreTateBundle.serreTateThm2'], axioms=['sorryAx'], sorry=True),
                         summary(72, 1, 1)))
        self.assertEqual(p['discharges'], [])
        self.assertEqual(len(p['rejected']), 1)
        self.assertIn('control character', p['rejected'][0])
        passed, reasons = discharges_log.evaluate(p)
        self.assertFalse(passed)
        self.assertTrue(any(r.startswith('a reporter line was rejected') for r in reasons), reasons)

    def test_other_control_characters_are_rejected(self):
        for name in ('a\rb', 'a\x1bb', 'a\u2028b', 'a\u202eb', 'a\x85b'):
            with self.subTest(name=repr(name)):
                p = parse(report(record(name, ['A.b']), summary(1, 1, 1)))
                self.assertEqual(p['discharges'], [])
                self.assertTrue(p['rejected'])
        p = parse(report(record('t', ['A.b\nc']), summary(1, 1, 1)))
        self.assertTrue(p['rejected'])

    def test_text_lines_and_other_nonces_do_not_count(self):
        forged = record('Contrib.fake', ['OpenGlue7.a'])
        text = (FORGED_TEXT + PASS_LOG + jline(forged, 'guess') + '\n' + 'x ' + jline(forged) + '\n'
                + ' ' + jline(forged) + '\n' + report(summary(67, 1, 0)))
        p = parse(text)
        self.assertEqual(p['discharges'], [])
        self.assertEqual(p['rejected'], [])
        self.assertEqual(discharges_log.evaluate(p)[1], ['no theorem discharges an open hypothesis'])

    def test_malformed_lines_are_rejected(self):
        bad = [
            'DISCHARGE-JSON %s {"theorem": ' % NONCE,
            'DISCHARGE-JSON %s [1, 2]' % NONCE,
            jline(dict(record('t', ['A.b']), sorry='no')),
            jline(dict(record('t', ['A.b']), extra=1)),
            jline(record('t', [])),
            jline(dict(record('t', ['A.b']), axioms='propext')),
            jline({'summary': {'open_hypotheses': '67', 'theorems_checked': 1, 'discharging': 0}}),
            jline({'summary': {'open_hypotheses': True, 'theorems_checked': 1, 'discharging': 0}}),
            'DISCHARGE-JSON %s {"theorem": "t", "theorem": "u", "hits": ["A.b"], "assumes": [], '
            '"axioms": [], "sorry": false}' % NONCE,
        ]
        for line in bad:
            with self.subTest(line=line):
                p = parse(line + '\n' + report(summary(1, 1, 0)))
                self.assertEqual(p['discharges'], [])
                self.assertEqual(len(p['rejected']), 1, p['rejected'])

    def test_summary_must_match_and_be_single(self):
        p = parse(report(record('t', ['A.b']), summary(1, 1, 2)))
        self.assertTrue(any('summary counts 2' in r for r in discharges_log.evaluate(p)[1]))
        p = parse(report(summary(1, 1, 0), summary(1, 1, 0)))
        self.assertIn('a second summary', p['rejected'][0])

    def test_missing_summary(self):
        p = parse(report(record('t', ['A.b'])))
        self.assertIn('the reporter printed no summary line', discharges_log.evaluate(p)[1])

    def test_errors_and_failed_reporter(self):
        log = 'Report.lean:3:7: error: unknown module prefix\n'
        passed, reasons = discharges_log.evaluate(parse(log), lean_status=1, lean_log=log)
        self.assertFalse(passed)
        self.assertIn('the reporter run failed (exit status 1)', reasons)
        self.assertIn('the reporter run reported 1 error(s)', reasons)

    def test_build_failure_and_real_sorry_warning(self):
        log = SORRY_LAKE + 'error: build failed\n'
        passed, reasons = discharges_log.evaluate(parse(''), build_status=1, lean_status=None,
                                                  build_log=log, added=ADDED)
        self.assertFalse(passed)
        self.assertEqual(reasons[0], 'the build failed (lake build exit status 1)')
        self.assertIn('the build log reports 1 error(s)', reasons)
        self.assertTrue(any('sorry in an added file' in r for r in reasons), reasons)

    def test_sorry_warning_forms(self):
        for log in (SORRY_LAKE, SORRY_LEAN, "warning: ZInQKernel/Contrib/OneProof/Foo.lean:1:1: "
                                            "declaration uses 'sorry'\n"):
            with self.subTest(log=log):
                self.assertEqual(len(discharges_log.sorry_warnings(log, ADDED)), 1)
        self.assertEqual(discharges_log.sorry_warnings(SORRY_LAKE, ['ZInQKernel/Contrib/OneProof/Bar.lean']), [])
        # A clean report still fails when the build log shows sorry in an added file.
        passed, reasons = discharges_log.evaluate(parse(PASS_REPORT), build_log=SORRY_LEAN, added=ADDED)
        self.assertFalse(passed)

    def test_text_parser_is_display_only(self):
        p = discharges_log.parse_text(PASS_LOG)
        d = p['discharges'][0]
        self.assertEqual(d['theorem'], 'Contrib.qp1_proof')
        self.assertEqual(d['still_assumes'], [
            '∀ (p : ℕ) [inst : Fact (Nat.Prime p)], HDec.Leaves.PrintedForm p (fun x => (x, x))',
            'HDec.Leaves.Other'])
        self.assertEqual(p['summary'], {'open_hypotheses': 67, 'theorems_checked': 4, 'discharging': 1})

    def test_lake_jobs_and_peak(self):
        self.assertEqual(discharges_log.lake_jobs('x\nBuild completed successfully (11712 jobs).\n'), 11712)
        self.assertEqual(discharges_log.lake_jobs('[1/30] Built A\n[29/31] Built B\n'), 31)
        self.assertIsNone(discharges_log.lake_jobs('nothing here'))
        self.assertEqual(discharges_log.peak_kib('\tMaximum resident set size (kbytes): 2048\n'), 2048)
        self.assertIsNone(discharges_log.peak_kib(''))

    def test_command_line(self):
        with tempfile.TemporaryDirectory() as d:
            log = os.path.join(d, 'log')
            with open(log, 'w') as fh:
                fh.write(PASS_LOG + PASS_REPORT)
            buf = io.StringIO()
            with redirect_stdout(buf):
                self.assertEqual(discharges_log.main([log, '--nonce', NONCE]), 0)
            self.assertEqual(json.loads(buf.getvalue())['discharges'][0]['theorem'], 'Contrib.qp1_proof')
            buf = io.StringIO()
            with redirect_stdout(buf):
                self.assertEqual(discharges_log.main([log]), 0)
            self.assertEqual(json.loads(buf.getvalue())['discharges'][0]['theorem'], 'Contrib.qp1_proof')
            with self.assertRaises(SystemExit):
                with redirect_stdout(io.StringIO()), unittest.mock.patch('sys.stderr', io.StringIO()):
                    discharges_log.main([log, '--result', os.path.join(d, 'r.json')])


FAKE_LAKE = '''#!/bin/sh
case "$1" in
  build) echo "fake lake $* nonce=${DISCHARGE_NONCE:-unset}"; echo "Build completed successfully (12 jobs)."
         exit "${FAKE_BUILD_STATUS:-0}" ;;
  env) case "$3" in
         *Report.lean) cat "$FAKE_REPORT_LOG"; exit "${FAKE_REPORT_STATUS:-0}" ;;
         *) echo "text run nonce=${DISCHARGE_NONCE:-unset}"; cat "$FAKE_LEAN_LOG" ;;
       esac ;;
  *) exit 3 ;;
esac
'''


class CheckScriptTest(unittest.TestCase):
    """discharge_check.sh end to end, with a stand-in for lake (nothing is built)."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        root = self.root = self.tmp.name
        sb = os.path.join(root, 'scripts', 'one_proof', 'sandbox')
        os.makedirs(sb)
        for name in ('discharge_check.sh', 'discharges_log.py', 'DischargesJson.lean'):
            shutil.copy(os.path.join(HERE, name), sb)
        self.write_render(0)
        os.makedirs(os.path.join(root, '.sandbox'))
        with open(os.path.join(root, '.sandbox', 'manifest.json'), 'w') as fh:
            json.dump({'base': 'b' * 40, 'head': 'h' * 40, 'pr': 7,
                       'added': ['ZInQKernel/Contrib/OneProof/Foo.lean',
                                 'ZInQKernel/Contrib/OneProof/Helper/Bar.lean',
                                 'ZInQKernel/Contrib/OneProof/Helper/LICENSE']}, fh)
        bindir = os.path.join(root, 'bin')
        os.makedirs(bindir)
        lake = os.path.join(bindir, 'lake')
        with open(lake, 'w') as fh:
            fh.write(FAKE_LAKE)
        os.chmod(lake, 0o755)
        env = dict(os.environ, PATH=bindir + os.pathsep + os.environ.get('PATH', ''),
                   FAKE_LEAN_LOG=os.path.join(root, 'lean.log'), FAKE_REPORT_LOG=os.path.join(root, 'report.log'),
                   DISCHARGE_NONCE=NONCE)
        self.env = env

    def tearDown(self):
        self.tmp.cleanup()

    def write_render(self, status):
        with open(os.path.join(self.root, 'scripts', 'one_proof', 'render_open.py'), 'w') as fh:
            fh.write("import sys\nprint('render check stand-in')\nsys.exit(%d)\n" % status)

    def out(self, name):
        with open(os.path.join(self.root, '.sandbox', 'out', name)) as fh:
            return fh.read()

    def run_check(self, report_log, build_status=0, mode=None, text_log=PASS_LOG, **env):
        with open(self.env['FAKE_LEAN_LOG'], 'w') as fh:
            fh.write(text_log)
        with open(self.env['FAKE_REPORT_LOG'], 'w') as fh:
            fh.write(report_log)
        e = dict(self.env, FAKE_BUILD_STATUS=str(build_status), **env)
        cmd = ['bash', os.path.join(self.root, 'scripts/one_proof/sandbox/discharge_check.sh')]
        if mode:
            cmd.append(mode)
        return subprocess.run(cmd, cwd=self.root, env=e, stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def result(self):
        return json.loads(self.out('result.json'))

    def test_pass(self):
        p = self.run_check(PASS_REPORT)
        self.assertEqual(p.returncode, 0, p.stdout.decode() + p.stderr.decode())
        result, log = self.result(), self.out('check.log')
        self.assertTrue(result['passed'])
        self.assertEqual(result['kind'], 'check')
        self.assertEqual(result['build']['lake_jobs'], 12)
        self.assertEqual(result['modules'], ['ZInQKernel.Contrib.OneProof.Foo',
                                             'ZInQKernel.Contrib.OneProof.Helper.Bar'])
        self.assertEqual(result['text_discharges'][0]['theorem'], 'Contrib.qp1_proof')
        self.assertIsInstance(result['seconds'], int)
        self.assertIn('fake lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges '
                      '+ZInQKernel.Contrib.OneProof.Foo +ZInQKernel.Contrib.OneProof.Helper.Bar nonce=unset', log)
        self.assertIn('text run nonce=unset', log)
        self.assertNotIn('nonce=' + NONCE, log)
        imports = ('import ZInQKernel.OneProof.Main\nimport ZInQKernel.OneProof.Discharges\n'
                   'import ZInQKernel.Contrib.OneProof.Foo\nimport ZInQKernel.Contrib.OneProof.Helper.Bar\n')
        with open(os.path.join(self.root, '.sandbox', 'Check.lean')) as fh:
            self.assertEqual(fh.read(), imports + '\n#discharges\n')
        with open(os.path.join(self.root, '.sandbox', 'Report.lean')) as fh:
            rep = fh.read()
        self.assertTrue(rep.startswith(imports))
        self.assertEqual(rep.count('import ZInQKernel.OneProof.Main'), 1)
        self.assertEqual(rep.rstrip().split('\n')[-1], '#discharges_json')

    def test_text_output_never_decides(self):
        p = self.run_check(EMPTY_REPORT, text_log=PASS_LOG)
        self.assertEqual(p.returncode, 1)
        self.assertEqual(self.result()['reasons'], ['no theorem discharges an open hypothesis'])
        p = self.run_check(PASS_REPORT, text_log=FORGED_TEXT)
        self.assertEqual(p.returncode, 0)

    def test_sorry_fails(self):
        p = self.run_check(SORRY_REPORT)
        self.assertEqual(p.returncode, 1)
        self.assertIn('t3 uses sorry', self.result()['reasons'])

    def test_render_check_is_information_only(self):
        self.write_render(1)
        p = self.run_check(PASS_REPORT)
        self.assertEqual(p.returncode, 0, p.stdout.decode() + p.stderr.decode())
        self.assertTrue(self.result()['passed'])
        self.assertEqual(self.result()['render_status'], 1)

    def test_build_error_fails(self):
        p = self.run_check(PASS_REPORT, build_status=1)
        self.assertEqual(p.returncode, 1)
        result = self.result()
        self.assertEqual(result['reasons'][0], 'the build failed (lake build exit status 1)')
        self.assertIsNone(result['lean_status'])
        self.assertFalse(os.path.exists(os.path.join(self.root, '.sandbox', 'Report.lean')))

    def test_separate_build_and_report_steps(self):
        p = self.run_check(PASS_REPORT, mode='build', DISCHARGE_NONCE='')
        self.assertEqual(p.returncode, 0, p.stderr.decode())
        self.assertFalse(os.path.exists(os.path.join(self.root, '.sandbox', 'out', 'result.json')))
        p = self.run_check(PASS_REPORT, mode='report')
        self.assertEqual(p.returncode, 0, p.stdout.decode() + p.stderr.decode())
        self.assertTrue(self.result()['passed'])

    def test_report_needs_the_nonce(self):
        p = self.run_check(PASS_REPORT, mode='build')
        self.assertEqual(p.returncode, 0)
        p = self.run_check(PASS_REPORT, mode='report', DISCHARGE_NONCE='')
        self.assertEqual(p.returncode, 1)
        self.assertIn('DISCHARGE_NONCE', p.stderr.decode())
        self.assertFalse(os.path.exists(os.path.join(self.root, '.sandbox', 'out', 'result.json')))

    def test_lines_with_another_nonce_do_not_count(self):
        p = self.run_check(report(record('Contrib.fake', ['OpenGlue7.a']), summary(67, 1, 1), nonce='other'))
        self.assertEqual(p.returncode, 1)
        self.assertIn('the reporter printed no summary line', self.result()['reasons'])

    def test_measure(self):
        os.remove(os.path.join(self.root, '.sandbox', 'manifest.json'))
        p = self.run_check('', mode='measure')
        self.assertEqual(p.returncode, 0, p.stdout.decode() + p.stderr.decode())
        result = self.result()
        self.assertEqual(result['kind'], 'measure')
        self.assertEqual(result['build']['status'], 0)
        self.assertEqual(result['build']['lake_jobs'], 12)
        self.assertFalse(result['build']['timed_out'])
        self.assertIsInstance(result['build']['seconds'], int)
        self.assertTrue(result['disk_before'] and result['disk_after'])
        self.assertIn('fake lake build +ZInQKernel.OneProof.Main', self.out('build.log'))


SCAN = {
    'base': 'a' * 40, 'head': 'c' * 40, 'merge_base': 'a' * 40, 'scope_ok': True, 'scope_problems': [],
    'files': [{'path': 'ZInQKernel/Contrib/OneProof/Foo.lean', 'bytes': 120, 'notes': [], 'hits': []}],
}


def result_for(text, scan=SCAN):
    parsed = parse(text)
    passed, reasons = discharges_log.evaluate(parsed)
    return {'kind': 'check', 'base': scan['base'], 'head': scan['head'], 'pr': 9, 'passed': passed,
            'reasons': reasons, 'discharges': parsed['discharges'], 'summary': parsed['summary'],
            'rejected': parsed['rejected'], 'text_discharges': [],
            'build': {'status': 0, 'seconds': 1500, 'lake_jobs': 11712, 'peak_kib': 8 * 1024 * 1024},
            'seconds': 1620, 'render_status': 0, 'lean_status': 0}


class CommentTest(unittest.TestCase):
    def common(self, text):
        self.assertNotIn('\u2014', text)  # no em-dash
        self.assertIn(discharge_comment.REMINDER, text)
        self.assertIn(discharge_comment.ADVISORY, text)
        # A job summary, not a post: it ends with the reminder, with no role line or footer.
        self.assertEqual(text.rstrip('\n').split('\n')[-1], discharge_comment.REMINDER)
        self.assertNotIn('Posted by', text)
        self.assertNotIn('project discharge check.', text)

    def test_pass_comment(self):
        res = dict(result_for(PASS_REPORT), pr='7 cc @elliotglazer [x](https://example.invalid)')
        text = discharge_comment.format_comment(SCAN, res, 'https://example.invalid/run/1', pr=9)
        self.common(text)
        self.assertIn('### Discharge check: pass\n', text)
        self.assertIn('`aaaaaaaaaaaa`', text)
        self.assertIn('`cccccccccccc`', text)
        self.assertIn('pull request #9.', text)
        self.assertNotIn('@elliotglazer', text)
        self.assertIn('Run: https://example.invalid/run/1', text)
        self.assertIn('- DISCHARGES `OpenGlue7.quotientP1Coordinate` by `Contrib.qp1_proof`', text)
        self.assertIn('still assumes: `∀ (p : ℕ) [inst : Fact (Nat.Prime p)], ', text)
        self.assertIn('axioms: `propext`, `Classical.choice`, `Quot.sound`', text)
        self.assertIn('11712 Lake jobs', text)
        self.assertIn('peak memory 8192 MiB', text)
        self.assertIn('no hits', text)
        self.assertNotIn(discharge_comment.HIT_SENTENCE, text)

    def test_hits_change_the_headline(self):
        scan = dict(SCAN, files=[dict(SCAN['files'][0], hits=[
            {'line': 4, 'kind': 'command:#eval', 'level': 'possible', 'text': '-- #eval IO.println "@someone"'}])])
        text = discharge_comment.format_comment(scan, result_for(PASS_REPORT, scan), pr=9)
        self.common(text)
        self.assertIn('### Discharge check: pass, which does not count while a file has scan hits\n', text)
        self.assertIn(discharge_comment.HIT_SENTENCE, text)
        self.assertIn('line `4`, `possible`, `command:#eval`: `-- #eval IO.println "@someone"`', text)

    def test_fail_comment(self):
        text = discharge_comment.format_comment(SCAN, result_for(SORRY_REPORT), pr=9)
        self.common(text)
        self.assertIn('### Discharge check: fail\n', text)
        self.assertIn('- `t3 uses sorry`', text)
        self.assertIn('(uses sorry: not a proof)', text)
        self.assertIn('still assumes: nothing', text)

    def test_code_spans_cannot_be_broken(self):
        self.assertEqual(discharge_comment.code('plain'), '`plain`')
        self.assertEqual(discharge_comment.code('a`b'), '`` a`b ``')
        evil = 'x```@elliotglazer [y](https://example.invalid) ```z'
        self.assertEqual(discharge_comment.code(evil), '```` %s ````' % evil)
        res = result_for(report(record(evil, ['OpenGlue7.a']), summary(1, 1, 1)))
        text = discharge_comment.format_comment(SCAN, res, pr=9)
        self.assertIn('by ```` %s ````' % evil, text)

    def test_malformed_result_is_no_result(self):
        good = result_for(PASS_REPORT)
        bad = [
            dict(good, summary={'open_hypotheses': '67', 'theorems_checked': 4, 'discharging': 1}),
            dict(good, build={'status': 0, 'seconds': 1, 'lake_jobs': '12'}),
            dict(good, passed='yes'),
            dict(good, discharges=[dict(good['discharges'][0], theorem=7)]),
            dict(good, discharges=[dict(good['discharges'][0], axioms='propext')]),
            dict(good, kind='measure'),
            dict(good, reasons=None),
            [1, 2],
        ]
        for res in bad:
            with self.subTest(res=res):
                text = discharge_comment.format_comment(SCAN, res, pr=9)
                self.common(text)
                self.assertIn('### Discharge check: no result\n', text)
                self.assertIn('does not have the expected shape', text)

    def test_out_of_scope_comment(self):
        scan = dict(SCAN, scope_ok=False, scope_problems=['modifies ZInQKernel/OneProof/Main.lean @x'])
        text = discharge_comment.format_comment(scan, None, pr=3)
        self.common(text)
        self.assertIn('### Discharge check: out of scope\n', text)
        self.assertIn('nothing was built', text)
        self.assertIn('add new files under `ZInQKernel/Contrib/OneProof/` and change nothing else', text)
        self.assertIn('- `modifies ZInQKernel/OneProof/Main.lean @x`', text)

    def test_mismatched_result(self):
        res = dict(result_for(PASS_REPORT), head='d' * 40)
        text = discharge_comment.format_comment(SCAN, res)
        self.assertIn('not the scanned pair', text)

    def test_render_status_is_information(self):
        res = dict(result_for(PASS_REPORT), render_status=1)
        text = discharge_comment.format_comment(SCAN, res)
        self.assertIn('### Discharge check: pass\n', text)
        self.assertIn('information for the maintainers only', text)

    def test_command_line(self):
        with tempfile.TemporaryDirectory() as d:
            sp, rp, op = (os.path.join(d, n) for n in ('scan.json', 'result.json', 'comment.md'))
            with open(sp, 'w') as fh:
                json.dump(SCAN, fh)
            with open(rp, 'w') as fh:
                json.dump(result_for(PASS_REPORT), fh)
            self.assertEqual(discharge_comment.main(['--scan', sp, '--result', rp, '--pr', '9', '--run-url', 'u',
                                                     '--out', op]), 0)
            with open(op) as fh:
                text = fh.read()
            self.common(text)
            self.assertIn('pull request #9.', text)
            with open(rp, 'w') as fh:
                fh.write('{"kind": "check", ')
            self.assertEqual(discharge_comment.main(['--scan', sp, '--result', rp, '--out', op]), 0)
            with open(op) as fh:
                self.assertIn('### Discharge check: no result\n', fh.read())


if __name__ == '__main__':
    unittest.main()
