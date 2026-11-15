"""Tests for scan_contrib.py and discharge_check.sh scope, on temporary git repositories (no network).

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
from contextlib import redirect_stdout, redirect_stderr

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import scan_contrib  # noqa: E402

GIT_ENV = {
    'GIT_AUTHOR_NAME': 'Test', 'GIT_AUTHOR_EMAIL': 'test@example.invalid',
    'GIT_COMMITTER_NAME': 'Test', 'GIT_COMMITTER_EMAIL': 'test@example.invalid',
    'GIT_CONFIG_NOSYSTEM': '1', 'GIT_CONFIG_GLOBAL': os.devnull,
}
_saved = {}
_template = {}


def setUpModule():
    for k, v in GIT_ENV.items():
        _saved[k] = os.environ.get(k)
        os.environ[k] = v
    # One base repository, copied for each test (git calls are the slow part).
    _template['dir'] = tempfile.TemporaryDirectory()
    _template['base'] = build_base(_template['dir'].name)


def tearDownModule():
    _template['dir'].cleanup()
    for k, v in _saved.items():
        if v is None:
            os.environ.pop(k, None)
        else:
            os.environ[k] = v


CONTRIB = 'ZInQKernel/Contrib/OneProof/'
CLEAN = '''import ZInQKernel.OneProof.Main

/-- A docstring. -/
theorem foo_proof : True := trivial
'''


class Repo:
    def __init__(self, path, init=True):
        self.path = path
        if init:
            self.git('init', '-q')
            self.git('config', 'commit.gpgsign', 'false')

    def git(self, *args):
        p = subprocess.run(['git', '-C', self.path] + list(args), stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE, check=True)
        return p.stdout.decode().strip()

    def write(self, rel, text):
        full = os.path.join(self.path, rel)
        os.makedirs(os.path.dirname(full), exist_ok=True)
        with open(full, 'w', encoding='utf-8') as fh:
            fh.write(text)

    def commit(self, msg):
        self.git('add', '-A')
        self.git('commit', '-q', '--allow-empty', '-m', msg)
        return self.git('rev-parse', 'HEAD')

    def plumb_commit(self, parent, files, msg='plumbing'):
        """A commit on top of parent adding files, made with git plumbing (for paths a case-insensitive or
        newline-hostile file system cannot hold)."""
        env = dict(os.environ, GIT_INDEX_FILE=os.path.join(self.path, '.git', 'test-index'))

        def run(*args, data=None):
            return subprocess.run(['git', '-C', self.path] + list(args), input=data, env=env, check=True,
                                  stdout=subprocess.PIPE, stderr=subprocess.PIPE).stdout.decode().strip()
        run('read-tree', parent)
        for path, text in files.items():
            blob = run('hash-object', '-w', '--stdin', data=text.encode())
            run('update-index', '--add', '--cacheinfo', '100644,%s,%s' % (blob, path))
        return run('commit-tree', run('write-tree'), '-p', parent, '-m', msg)


def build_base(path):
    r = Repo(path)
    r.write('README.md', 'base readme\n')
    r.write('ZInQKernel/OneProof/Main.lean', 'theorem main : True := trivial\n')
    r.write(CONTRIB + 'Existing.lean', 'theorem existing : True := trivial\n')
    r.write('.github/workflows/ci.yml', 'name: ci\n')
    return r.commit('base')


def make_base(path):
    shutil.copytree(_template['dir'].name, path, symlinks=True, dirs_exist_ok=True)
    return Repo(path, init=False), _template['base']


class ScopeTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.repo, self.base = make_base(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def scan(self, head):
        return scan_contrib.scan(self.base, head, self.tmp.name)

    def test_in_scope_addition(self):
        self.repo.write(CONTRIB + 'Foo.lean', CLEAN)
        self.repo.write(CONTRIB + 'Helper/LICENSE', 'Apache-2.0\n')
        head = self.repo.commit('add')
        res = self.scan(head)
        self.assertTrue(res['scope_ok'], res['scope_problems'])
        self.assertEqual(res['merge_base'], self.base)
        by_path = {f['path']: f for f in res['files']}
        self.assertEqual(set(by_path), {CONTRIB + 'Foo.lean', CONTRIB + 'Helper/LICENSE'})
        self.assertEqual(by_path[CONTRIB + 'Foo.lean']['hits'], [])
        self.assertEqual(by_path[CONTRIB + 'Helper/LICENSE']['type'], 'text')
        self.assertEqual(by_path[CONTRIB + 'Foo.lean']['bytes'], len(CLEAN.encode()))
        with redirect_stdout(io.StringIO()):
            self.assertEqual(scan_contrib.main([self.base, head, '--repo', self.tmp.name]), 0)

    def test_hits_do_not_change_exit_code(self):
        self.repo.write(CONTRIB + 'Foo.lean', CLEAN + '#eval 1\n')
        head = self.repo.commit('add')
        out = os.path.join(self.tmp.name, 'scan.json')
        with redirect_stdout(io.StringIO()):
            code = scan_contrib.main([self.base, head, '--repo', self.tmp.name, '--json', out])
        self.assertEqual(code, 0)
        with open(out) as fh:
            res = json.load(fh)
        self.assertEqual([h['kind'] for h in res['files'][0]['hits']], ['command:#eval'])
        self.assertEqual(res['files'][0]['hits'][0]['line'], 5)

    def test_merge_base_is_used(self):
        self.repo.write(CONTRIB + 'Foo.lean', CLEAN)
        head = self.repo.commit('add')
        self.repo.git('checkout', '-q', '-b', 'later', self.base)
        self.repo.write('README.md', 'base moved on\n')
        later = self.repo.commit('later')
        res = scan_contrib.scan(later, head, self.tmp.name)
        self.assertTrue(res['scope_ok'], res['scope_problems'])
        self.assertEqual(res['merge_base'], self.base)

    def assertOut(self, head, word):
        out = os.path.join(self.tmp.name, 'scan.json')
        with redirect_stdout(io.StringIO()):
            self.assertEqual(scan_contrib.main([self.base, head, '--repo', self.tmp.name, '--json', out]), 2)
        with open(out) as fh:
            res = json.load(fh)
        self.assertFalse(res['scope_ok'])
        self.assertTrue(any(word in p for p in res['scope_problems']), res['scope_problems'])

    def test_modification_is_out(self):
        self.repo.write(CONTRIB + 'Existing.lean', 'theorem existing : True := by trivial\n')
        self.assertOut(self.repo.commit('modify'), 'modifies')

    def test_deletion_is_out(self):
        self.repo.git('rm', '-q', CONTRIB + 'Existing.lean')
        self.assertOut(self.repo.commit('delete'), 'deletes')

    def test_rename_is_out(self):
        self.repo.git('mv', CONTRIB + 'Existing.lean', CONTRIB + 'Renamed.lean')
        self.assertOut(self.repo.commit('rename'), 'renames')

    def test_path_outside_is_out(self):
        self.repo.write(CONTRIB + 'Foo.lean', CLEAN)
        self.repo.write('docs/notes.md', 'x\n')
        self.assertOut(self.repo.commit('outside'), 'outside')

    def test_workflow_change_is_out(self):
        self.repo.write(CONTRIB + 'Foo.lean', CLEAN)
        self.repo.write('.github/workflows/evil.yml', 'name: evil\n')
        self.assertOut(self.repo.commit('workflow'), 'outside')

    def test_symlink_is_out(self):
        os.makedirs(os.path.join(self.tmp.name, CONTRIB), exist_ok=True)
        os.symlink('../../../README.md', os.path.join(self.tmp.name, CONTRIB + 'Link.lean'))
        self.assertOut(self.repo.commit('symlink'), 'symlink')

    def test_mode_change_is_out(self):
        os.chmod(os.path.join(self.tmp.name, CONTRIB + 'Existing.lean'), 0o755)
        self.assertOut(self.repo.commit('chmod'), 'modifies')

    def test_executable_addition_is_out(self):
        self.repo.write(CONTRIB + 'Foo.lean', CLEAN)
        os.chmod(os.path.join(self.tmp.name, CONTRIB + 'Foo.lean'), 0o755)
        self.assertOut(self.repo.commit('exec'), 'executable')

    def test_odd_lean_path_is_out(self):
        self.repo.write(CONTRIB + 'Bad-Name.lean', CLEAN)
        self.assertOut(self.repo.commit('odd'), 'plain module path')

    def test_non_text_helper_is_out(self):
        self.repo.write(CONTRIB + 'Foo.lean', CLEAN)
        self.repo.write(CONTRIB + 'Helper/build.sh', 'echo hi\n')
        self.assertOut(self.repo.commit('script'), 'neither')

    def test_text_file_at_top_is_out(self):
        self.repo.write(CONTRIB + 'Foo.lean', CLEAN)
        self.repo.write(CONTRIB + 'README.md', 'x\n')
        self.assertOut(self.repo.commit('readme'), 'neither')

    def test_no_lean_file_is_out(self):
        self.repo.write(CONTRIB + 'Helper/README.md', 'x\n')
        self.assertOut(self.repo.commit('readme only'), 'no Lean file')

    def test_clash_with_base_is_out(self):
        self.repo.write(CONTRIB + 'Foo.lean', CLEAN)
        head = self.repo.commit('add')
        self.repo.git('checkout', '-q', '-b', 'later', self.base)
        self.repo.write(CONTRIB + 'Foo.lean', 'theorem other : True := trivial\n')
        later = self.repo.commit('base gets Foo')
        res = scan_contrib.scan(later, head, self.tmp.name)
        self.assertFalse(res['scope_ok'])
        self.assertIn('already exists', res['scope_problems'][0])

    def test_case_clash_with_base_is_out(self):
        head = self.repo.plumb_commit(self.base, {CONTRIB + 'existing.lean': CLEAN})
        self.assertOut(head, 'already exists')
        head = self.repo.plumb_commit(self.base, {CONTRIB + 'EXISTING.lean/Sub.lean': CLEAN})
        self.assertOut(head, 'already exists')

    def test_case_clash_within_the_diff_is_out(self):
        head = self.repo.plumb_commit(self.base, {CONTRIB + 'Foo.lean': CLEAN, CONTRIB + 'foo.lean': CLEAN})
        self.assertOut(head, 'another added path')

    def test_newline_in_path_is_out(self):
        head = self.repo.plumb_commit(self.base, {CONTRIB + 'Foo.lean': CLEAN,
                                                  CONTRIB + 'Sub/README.md\n': 'x\n'})
        self.assertOut(head, 'control character')

    def test_path_patterns_end_at_the_end(self):
        self.assertIsNone(scan_contrib.LEAN_PATH_RE.match(CONTRIB + 'Foo.lean\n'))
        self.assertIsNone(scan_contrib.TEXT_PATH_RE.match(CONTRIB + 'Sub/README.md\n'))
        self.assertIsNotNone(scan_contrib.LEAN_PATH_RE.match(CONTRIB + 'Sub/Foo_2.lean'))

    def test_bad_revision_is_an_error(self):
        with redirect_stderr(io.StringIO()):
            self.assertEqual(scan_contrib.main([self.base, 'no-such-rev', '--repo', self.tmp.name]), 1)


def kinds(src):
    return [h['kind'] for h in scan_contrib.scan_lean(src)[0]]


def likely(src):
    return [h['kind'] for h in scan_contrib.scan_lean(src)[0] if h['level'] == 'likely']


def possible(src):
    return [h['kind'] for h in scan_contrib.scan_lean(src)[0] if h['level'] == 'possible']


class PatternTest(unittest.TestCase):
    CASES = [
        ('run_cmd Lean.logInfo "hi"', 'command:run_cmd'),
        ('theorem t : True := by\n  run_tac Lean.Elab.Tactic.evalTactic default', 'command:run_tac'),
        ('run_elab pure ()', 'command:run_elab'),
        ('run_meta pure ()', 'command:run_meta'),
        ('#eval IO.println "x"', 'command:#eval'),
        ('#eval! (1 : Nat)', 'command:#eval!'),
        ('syntax "foo" : term', 'command:syntax'),
        ('macro "foo" : term => `(1)', 'command:macro'),
        ('macro_rules | `(foo) => `(2)', 'command:macro_rules'),
        ('elab "foo" : term => pure default', 'command:elab'),
        ('elab_rules : term | `(foo) => pure default', 'command:elab_rules'),
        ('notation "ell" => 1', 'command:notation'),
        ('notation3 "ell" => 1', 'command:notation3'),
        ('infix:65 " +++ " => Nat.add', 'command:infix'),
        ('infixl:65 " +++ " => Nat.add', 'command:infixl'),
        ('infixr:65 " +++ " => Nat.add', 'command:infixr'),
        ('prefix:max "sq" => Nat.sqrt', 'command:prefix'),
        ('postfix:max "!!" => Nat.succ', 'command:postfix'),
        ('initialize counter : IO.Ref Nat <- IO.mkRef 0', 'command:initialize'),
        ('builtin_initialize pure ()', 'command:builtin_initialize'),
        ('local notation "x" => 1', 'command:notation'),
        ('scoped infix:50 " ~~ " => Eq', 'command:infix'),
        ('private macro "bar" : term => `(3)', 'command:macro'),
        ('protected syntax "baz" : term', 'command:syntax'),
        ('@[simp] macro "q" : term => `(4)', 'command:macro'),
        ('open Lean in\nelab "foo" : command => pure ()', 'command:elab'),
        ('declare_syntax_cat mycat', 'command:declare_syntax_cat'),
        ('simproc reduceFoo (foo _) := fun _ => pure .continue', 'command:simproc'),
        ('@[command_elab foo] def f : Lean.Elab.Command.CommandElab := fun _ => pure ()',
         'attribute:command_elab'),
        ('@[term_elab foo] def f := 1', 'attribute:term_elab'),
        ('@[tactic foo] def f := 1', 'attribute:tactic'),
        ('@[macro foo] def f := 1', 'attribute:macro'),
        ('@[delab app.foo] def f := 1', 'attribute:delab'),
        ('@[app_unexpander foo] def f := 1', 'attribute:app_unexpander'),
        ('@[implemented_by g] def f := 1', 'attribute:implemented_by'),
        ('@[extern "c_f"] def f := 1', 'attribute:extern'),
        ('@[init g] def f := 1', 'attribute:init'),
        ('@[builtin_init g] def f := 1', 'attribute:builtin_init'),
        ('@[env_linter] def f := 1', 'attribute:env_linter'),
        ('@[linter] def f := 1', 'attribute:linter'),
        ('@[code_action_provider] def f := 1', 'attribute:code_action_provider'),
        ('@[code_action] def f := 1', 'attribute:code_action'),
        ('@[simp,\n  tactic foo] def f := 1', 'attribute:tactic'),
        ('attribute [tactic foo] bar', 'attribute:tactic'),
        ('attribute [local macro foo] bar', 'attribute:macro'),
        ('@[positivity _ + _] def evalAdd := 1', 'attribute:positivity'),
        ('axiom bad : False', 'word:axiom'),
        ('private axiom bad : False', 'word:axiom'),
        ('unsafe def f : Nat := 1', 'word:unsafe'),
        ('theorem t : 2 + 2 = 4 := by native_decide', 'word:native_decide'),
        ('theorem t : True := Lean.ofReduceBool _ _ rfl', 'word:ofReduceBool'),
        ('theorem t : True := implemented_by', 'word:implemented_by'),
        ('set_option debug.skipKernelTC true', 'word:skipKernelTC'),
        # every # command but #check and #print
        ('#guard (unsafeBaseIO (pure true))', 'command:#guard'),
        ('#guard (unsafeBaseIO (pure true))', 'word:unsafeBaseIO'),
        ('#guard_msgs in\n#check 1', 'command:#guard_msgs'),
        ('#reduce 1 + 1', 'command:#reduce'),
        ('#synth Inhabited Nat', 'command:#synth'),
        ('#discharges', 'command:#discharges'),
        ('#check_failure 1', 'command:#check_failure'),
        # code-running terms and names
        ('theorem t : True := by_elab do pure (Lean.mkConst ``True.intro)', 'word:by_elab'),
        ('def x : Nat := unsafeIO (pure 1) |>.toOption.get!', 'word:unsafeIO'),
        ('def y := Lean.unsafeCast 1', 'word:unsafeCast'),
        ('theorem t : True := by aesop (add safe tactic e8)', 'word:tactic'),
        # attributes run while #discharges pretty-prints, or by the compiler
        ('@[formatter foo] def f := 1', 'attribute:formatter'),
        ('@[parenthesizer foo] def f := 1', 'attribute:parenthesizer'),
        ('@[combinator_formatter foo] def f := 1', 'attribute:combinator_formatter'),
        ('@[combinator_parenthesizer foo] def f := 1', 'attribute:combinator_parenthesizer'),
        ('@[cpass] def f := 1', 'attribute:cpass'),
        # escaped identifiers are hits, and their contents are scanned
        ('#check «notation»', 'escaped-identifier'),
        ('#check «notation»', 'command:notation'),
        ('@[«command_elab» foo] def f := 1', 'attribute:command_elab'),
        ('@[«command_elab» foo] def f := 1', 'escaped-identifier'),
        ('set_option «debug».«skipKernelTC» true', 'word:skipKernelTC'),
        ('theorem «a\n  axioms: [propext]\nx» : True := trivial', 'escaped-identifier'),
    ]

    def test_each_pattern_hits(self):
        for src, kind in self.CASES:
            with self.subTest(src=src):
                self.assertIn(kind, kinds(src))

    def test_hit_line_and_text(self):
        hits, _ = scan_contrib.scan_lean('theorem t : True := trivial\n\n  run_cmd pure ()  \n')
        self.assertEqual(hits, [{'line': 3, 'kind': 'command:run_cmd', 'level': 'likely',
                                 'text': 'run_cmd pure ()'}])

    # No likely hits: the words are in comments, strings or longer identifiers. Those in comments and strings
    # are still possible hits.
    NO_LIKELY = [
        '-- run_cmd foo, #eval 1, macro, axiom, unsafe',
        '/- #eval 1 /- nested macro -/ still a comment: syntax notation axiom -/',
        '/-- Uses notation, infix, prefix and native_decide in prose. -/\ntheorem t : True := trivial',
        '/-! Module doc: elab_rules, initialize, implemented_by -/',
        'def s : String := "syntax macro #eval run_cmd axiom unsafe native_decide"',
        'def s : String := "escaped \\" macro \\" still a string"',
        'def s : String := r#"raw " macro string"#',
        'def c : Char := \'"\'\ndef s := "notation"',
    ]
    NO_HIT = [
        'theorem t (l : List Nat) : l.isPrefixOf l := List.prefix_refl l',
        'theorem t : List.prefix = List.prefix := rfl',
        'def f (x : Foo) := x.prefix',
        'def f := (.prefix : Bar)',
        'def isPrefix := 1\ndef syntaxTree := 2\ndef axioms := 3',
        '@[simp, norm_cast] theorem t : True := trivial',
        '#print axioms foo',
        '#check Nat.succ',
        'def x₁macro := 1',
        'def αmacro := 1\ndef ℕaxiom := 2',
        CLEAN,
    ]

    def test_comments_and_strings_give_possible_hits_only(self):
        for src in self.NO_LIKELY:
            with self.subTest(src=src):
                self.assertEqual(likely(src), [])
                self.assertNotEqual(possible(src), [])

    def test_no_hits_in_identifiers(self):
        for src in self.NO_HIT:
            with self.subTest(src=src):
                self.assertEqual(kinds(src), [])

    def test_lean_identifier_boundaries(self):
        # λ is not an identifier character in Lean, though Python counts it as a letter.
        self.assertIn('command:macro', likely('def f := λmacro => 1'))
        # U+1D40 ends the identifier, so r#"..."# is a raw string and the run_cmd after it is code.
        src = 'def s := A\u1d40r#"\\"#\nrun_cmd pure ()\ndef t := "x"\n'
        self.assertIn(('command:run_cmd', 2), [(h['kind'], h['line']) for h in scan_contrib.scan_lean(src)[0]
                                                if h['level'] == 'likely'])

    def test_interpolation_heads(self):
        for src in ('def f : MetaM Unit := throwError "{(by native_decide : 2 = 2)}"',
                    'def f (s : Syntax) : MetaM Unit := throwErrorAt s "{(by native_decide : 2 = 2)}"',
                    'def f : MetaM Unit := Lean.throwError "{(by native_decide : 2 = 2)}"',
                    'def f : Nat := dbg_trace "{(by native_decide : 2 = 2)}"; 1',
                    'def f : MetaM Unit := do\n  throwError\n    "{(by native_decide : 2 = 2)}"',
                    'def f := println! "{(by native_decide : 2 = 2)}"',
                    'def f := m!"{(by native_decide : 2 = 2)}"'):
            with self.subTest(src=src):
                self.assertIn('word:native_decide', likely(src))

    def test_nested_string_in_braces(self):
        src = 'def s := s!"{"}" ++ x}"\nrun_cmd pure ()\n'
        hits = scan_contrib.scan_lean(src)[0]
        self.assertIn(('command:run_cmd', 2, 'likely'), [(h['kind'], h['line'], h['level']) for h in hits])

    def test_unterminated_tokens_are_hits(self):
        for src, kind in (('def s := "abc', 'lexer:unterminated string literal'),
                          ('/- open comment', 'lexer:unterminated block comment'),
                          ('def x := «abc', 'lexer:unterminated escaped identifier'),
                          ('def s := r#"abc', 'lexer:unterminated raw string'),
                          ('def s := s!"{ x', 'lexer:unterminated interpolation brace')):
            with self.subTest(src=src):
                self.assertIn(kind, likely(src))

    def test_lexer_disagreement_gives_a_possible_hit(self):
        # A macro that takes an interpolated string under a name the scanner does not know: the stripper
        # reads a plain string and blanks it, and the raw pass still reports what is inside.
        src = 'def f := myInterp "{run_cmd}"\n'
        hits = scan_contrib.scan_lean(src)[0]
        self.assertEqual(likely(src), [])
        self.assertEqual([(h['kind'], h['level']) for h in hits], [('command:run_cmd', 'possible')])

    def test_likely_hit_is_not_repeated_as_possible(self):
        hits = scan_contrib.scan_lean('#eval 1\n')[0]
        self.assertEqual([(h['kind'], h['level']) for h in hits], [('command:#eval', 'likely')])

    def test_char_literal_does_not_open_a_string(self):
        hits, _ = scan_contrib.scan_lean('def c : Char := \'"\'\nrun_cmd pure ()\n')
        self.assertEqual([(h['line'], h['kind']) for h in hits], [(2, 'command:run_cmd')])

    def test_interpolated_term_is_scanned(self):
        self.assertIn('word:native_decide', kinds('def s := s!"{(by native_decide : 2 = 2)}"'))

    def test_import_lean_is_a_note(self):
        hits, notes = scan_contrib.scan_lean('import Lean\nimport Mathlib\ntheorem t : True := trivial\n')
        self.assertEqual(hits, [])
        self.assertTrue(any('imports Lean' in n for n in notes), notes)

    def test_large_file_note(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        repo, base = make_base(tmp.name)
        repo.write(CONTRIB + 'Big.lean', CLEAN + ('-- padding\n' * 16000))
        head = repo.commit('big')
        res = scan_contrib.scan(base, head, tmp.name)
        self.assertTrue(res['scope_ok'])
        self.assertTrue(any('150 KB' in n for n in res['files'][0]['notes']))


class ScopeModeTest(unittest.TestCase):
    """discharge_check.sh scope: the scan, then the manifest the build reads, in scope only."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.repo, self.base = make_base(self.tmp.name)
        sb = os.path.join(self.tmp.name, 'scripts', 'one_proof', 'sandbox')
        os.makedirs(sb)
        for name in ('discharge_check.sh', 'scan_contrib.py'):
            shutil.copy(os.path.join(HERE, name), sb)
        self.script = os.path.join(sb, 'discharge_check.sh')
        self.manifest = os.path.join(self.tmp.name, '.sandbox', 'manifest.json')

    def tearDown(self):
        self.tmp.cleanup()

    def run_scope(self, head):
        return subprocess.run(['bash', self.script, 'scope', self.base, head], cwd=self.tmp.name,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    def scan_json(self):
        with open(os.path.join(self.tmp.name, '.sandbox', 'out', 'scan.json')) as fh:
            return json.load(fh)

    def test_in_scope_writes_the_manifest(self):
        head = self.repo.plumb_commit(self.base, {CONTRIB + 'Foo.lean': CLEAN, CONTRIB + 'Helper/README.md': 'h\n'})
        p = self.run_scope(head)
        self.assertEqual(p.returncode, 0, p.stderr.decode())
        self.assertTrue(self.scan_json()['scope_ok'])
        with open(self.manifest) as fh:
            self.assertEqual(json.load(fh), {'base': self.base, 'head': head,
                                             'added': [CONTRIB + 'Foo.lean', CONTRIB + 'Helper/README.md']})

    def test_out_of_scope_writes_no_manifest(self):
        os.makedirs(os.path.dirname(self.manifest))
        with open(self.manifest, 'w') as fh:
            fh.write('{"added": []}\n')
        head = self.repo.plumb_commit(self.base, {CONTRIB + 'Foo.lean': CLEAN, 'README.md': 'changed\n'})
        p = self.run_scope(head)
        self.assertEqual(p.returncode, 2, p.stderr.decode())
        self.assertFalse(self.scan_json()['scope_ok'])
        self.assertFalse(os.path.exists(self.manifest))

    def test_needs_base_and_head(self):
        p = subprocess.run(['bash', self.script, 'scope', self.base], cwd=self.tmp.name, stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE)
        self.assertEqual(p.returncode, 1)
        self.assertIn('usage', p.stderr.decode())


if __name__ == '__main__':
    unittest.main()
