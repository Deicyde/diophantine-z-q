"""Scope gate and build-time-code scan for a contribution pull request, on git objects only.

Usage: python3 scan_contrib.py BASE HEAD [--repo DIR] [--json OUT]

Nothing is checked out, built or run: the script reads the diff between the merge base of BASE and HEAD
and HEAD, and the added blobs, with git plumbing commands.

Scope gate: every changed path must be an ADDITION under ZInQKernel/Contrib/OneProof/: Lean files (whose
path is a plain module path), or plain-text files such as LICENSE, NOTICE or README.md in a helper directory
there (they pass and are listed). A modification, deletion, rename, copy, mode or type change, symlink,
submodule, executable file, a path outside that directory, a path with a control character, or a path that
already exists in BASE or in the same diff when compared without case makes the pull request out of scope. So
does a diff that adds no Lean file.

Scan (advisory): each added .lean file is searched for code that runs at build time: every `#` command but
#check and #print; commands such as run_cmd, syntax, macro, elab, notation, initialize; attributes that
register elaborators, macros, tactics, delaborators, formatters, parenthesizers, compiler passes, linters or
native code; the words axiom, by_elab, tactic, native_decide, ofReduceBool, implemented_by and any name
starting with unsafe; and every escaped identifier (guillemets). A hit is "likely" when it lies outside
comments and strings as this script's lexer reads them, and "possible" when it is found only in the raw text
(comments and strings included), so a disagreement with Lean's lexer can add hits but never hide one. An
unterminated string, comment, escaped identifier or interpolation brace is a hit. Matching is by token and
prefix, with Lean's identifier characters, and errs towards false positives. A clean scan does not show that
a file is safe. `import Lean` is a note, never a hit. Files over 150 KB get a note.

Output: JSON {base, head, merge_base, scope_ok, scope_problems, files: [{path, bytes, hits: [{line, kind,
level, text}], notes, ...}]} written to OUT ("-" for standard output), and a short text summary.
Exit status: 0 in scope (hits do not change it), 2 out of scope, 1 on error.
"""
import argparse
import json
import re
import subprocess
import sys
import unicodedata

PREFIX = 'ZInQKernel/Contrib/OneProof/'
IDENT = r'[A-Za-z_][A-Za-z0-9_]*'
LEAN_PATH_RE = re.compile(r'ZInQKernel/Contrib/OneProof/(?:%s/)*%s\.lean\Z' % (IDENT, IDENT))
TEXT_PATH_RE = re.compile(r'ZInQKernel/Contrib/OneProof/(?:%s/)+([A-Za-z0-9][A-Za-z0-9_.-]*)\Z' % IDENT)
TEXT_STEMS = {'LICENSE', 'LICENCE', 'NOTICE', 'README', 'COPYING', 'AUTHORS', 'CREDITS'}
TEXT_EXTS = {'.md', '.txt'}
MAX_BYTES = 150 * 1024

# Commands that define syntax or run code while a file elaborates. A bare token equal to one of these, or
# starting with one of the prefixes, is a hit. Every `#` command except these two is a hit as well.
HASH_ALLOWED = {'#check', '#print'}
COMMANDS = {
    'syntax', 'macro', 'macro_rules', 'elab', 'elab_rules', 'notation', 'infix', 'infixl', 'infixr',
    'prefix', 'postfix', 'initialize', 'builtin_initialize', 'simproc', 'dsimproc', 'simproc_decl',
    'dsimproc_decl', 'binder_predicate', 'meta',
}
COMMAND_PREFIXES = ('run_', 'elab_', 'macro_', 'syntax_', 'initialize_', 'builtin_', 'register_',
                    'declare_', 'simproc', 'dsimproc', 'notation', 'infix')
# Words that are a hit anywhere, also as a component of a dotted name (Lean.ofReduceBool); so is any
# component starting with `unsafe` (unsafeBaseIO, unsafeIO, unsafeCast).
WORDS = {'axiom', 'native_decide', 'ofReduceBool', 'ofReduceNat', 'implemented_by', 'trustCompiler',
         'skip' 'KernelTC', 'by_elab', 'tactic'}
# Attribute names that register code run at build time (or replace compiled code).
ATTRS = {'command_elab', 'term_elab', 'tactic', 'macro', 'delab', 'app_delab', 'app_unexpander',
         'implemented_by', 'extern', 'export', 'init', 'builtin_init', 'env_linter', 'linter', 'code_action',
         'csimp', 'simproc', 'dsimproc', 'command_parser', 'term_parser', 'tactic_parser', 'positivity',
         'norm_num', 'formatter', 'parenthesizer', 'combinator_formatter', 'combinator_parenthesizer', 'cpass'}
ATTR_PREFIXES = ('builtin_', 'code_action')
ATTR_SUFFIXES = ('_elab', '_parser', '_delab', '_unexpander', '_linter', '_init', 'simproc', '_code_action',
                 '_formatter', '_parenthesizer')
# A string after one of these (on the same line, or as the token just before it), or after a `!` prefix
# (s!, m!, f!, println!), may be interpolated: its {...} parts are code.
INTERP_HEADS = {'throwError', 'throwErrorAt', 'throwNamedError', 'throwNamedErrorAt', 'logNamedError',
                'logNamedErrorAt', 'logNamedWarning', 'logNamedWarningAt', 'dbg_trace', 'trace'}
INTERP_LINE_RE = re.compile(r"(?<![A-Za-z0-9_'!?])(?:%s)(?![A-Za-z0-9_'!?])" % '|'.join(sorted(INTERP_HEADS)))

CHAR_RE = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'")
RAW_RE = re.compile(r'r(#*)"')
IMPORT_RE = re.compile(r"(?<![\w'!?.])import\s+(\S+)")
CONTROL_CATEGORIES = ('Cc', 'Cf', 'Zl', 'Zp', 'Cs')


class GitError(Exception):
    pass


def git(repo, *args):
    cmd = ['git']
    if repo:
        cmd += ['-C', repo]
    cmd += list(args)
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if p.returncode != 0:
        raise GitError('%s: %s' % (' '.join(cmd), p.stderr.decode('utf-8', 'replace').strip()))
    return p.stdout


# Lean's identifier characters (Init/Meta/Defs.lean: isLetterLike, isSubScriptAlnum, isIdFirst, isIdRest).
def is_letter_like(c):
    u = ord(c)
    return ((0x3b1 <= u <= 0x3c9 and u != 0x3bb) or (0x391 <= u <= 0x3a9 and u not in (0x3a0, 0x3a3))
            or 0x3ca <= u <= 0x3fb or 0x1f00 <= u <= 0x1ffe or 0x2100 <= u <= 0x214f
            or 0x1d49c <= u <= 0x1d59f or (0xc0 <= u <= 0xff and u not in (0xd7, 0xf7)) or 0x100 <= u <= 0x17f)


def is_sub_alnum(c):
    u = ord(c)
    return 0x2080 <= u <= 0x2089 or 0x2090 <= u <= 0x209c or 0x1d62 <= u <= 0x1d6a or u == 0x2c7c


def is_id_first(c):
    return 'a' <= c <= 'z' or 'A' <= c <= 'Z' or c == '_' or is_letter_like(c)


def is_id_rest(c):
    return is_id_first(c) or '0' <= c <= '9' or c in "'!?" or is_sub_alnum(c)


def has_control(s):
    return any(unicodedata.category(c) in CONTROL_CATEGORIES for c in s)


def printable(s):
    """s with control characters written as escapes, for the terminal summary."""
    return ''.join(ascii(c)[1:-1] if unicodedata.category(c) in CONTROL_CATEGORIES else c for c in s)


class Lexer:
    """Blank out comments, string literals and char literals, keeping line structure and the code inside
    interpolation braces. Guillemets of escaped identifiers are blanked and their contents kept.
    Records unterminated tokens in `problems` and the position of each escaped identifier in `escapes`."""

    def __init__(self, src):
        self.src = src
        self.n = len(src)
        self.out = list(src)
        self.problems = []
        self.escapes = []

    def run(self):
        self.code(0, False)
        return ''.join(self.out)

    def blank(self, a, b):
        for k in range(a, min(b, self.n)):
            if self.out[k] != '\n':
                self.out[k] = ' '

    def interpolated(self, i):
        src = self.src
        k = i - 1
        while k >= 0 and src[k].isspace():
            k -= 1
        if k >= 0 and src[k] == '!':
            return True
        end = k + 1
        while k >= 0 and (is_id_rest(src[k]) or src[k] == '.'):
            k -= 1
        if src[k + 1:end].split('.')[-1] in INTERP_HEADS:
            return True
        line_start = src.rfind('\n', 0, i) + 1
        return bool(INTERP_LINE_RE.search(src, line_start, i))

    def code(self, i, in_brace):
        """Lex code from i; inside an interpolation brace, stop after the matching '}'."""
        src, n = self.src, self.n
        start = i
        depth = 0
        while i < n:
            c = src[i]
            if c == '-' and src.startswith('--', i):
                j = src.find('\n', i)
                j = n if j < 0 else j
                self.blank(i, j)
                i = j
                continue
            if c == '/' and src.startswith('/-', i):
                d, j = 1, i + 2
                while j < n and d:
                    if src.startswith('/-', j):
                        d += 1
                        j += 2
                    elif src.startswith('-/', j):
                        d -= 1
                        j += 2
                    else:
                        j += 1
                if d:
                    self.problems.append((i, 'unterminated block comment'))
                self.blank(i, j)
                i = j
                continue
            if in_brace and c == '{':
                depth += 1
            elif in_brace and c == '}':
                if depth == 0:
                    return i + 1
                depth -= 1
            if c == '«':  # «name»: Lean reads up to the closing guillemet
                self.escapes.append(i)
                self.out[i] = ' '
                j = src.find('»', i + 1)
                if j < 0:
                    self.problems.append((i, 'unterminated escaped identifier'))
                    i += 1
                    continue
                self.out[j] = ' '
                i = j + 1
                continue
            if c == 'r' and (i == 0 or not is_id_rest(src[i - 1])):
                m = RAW_RE.match(src, i)
                if m:
                    end = '"' + m.group(1)
                    j = src.find(end, m.end())
                    if j < 0:
                        self.problems.append((i, 'unterminated raw string'))
                        j = n
                    else:
                        j += len(end)
                    self.blank(i, j)
                    i = j
                    continue
            if c == '"':
                i = self.string(i, self.interpolated(i))
                continue
            if c == "'" and (i == 0 or not is_id_rest(src[i - 1])):
                m = CHAR_RE.match(src, i)
                if m:
                    self.blank(i, m.end())
                    i = m.end()
                    continue
            i += 1
        if in_brace:
            self.problems.append((start, 'unterminated interpolation brace'))
        return n

    def string(self, i, interp):
        src, n = self.src, self.n
        j = i + 1
        seg = i  # start of the literal part not yet blanked
        while j < n:
            ch = src[j]
            if ch == '"':
                self.blank(seg, j + 1)
                return j + 1
            if ch == '\\':
                j += 2
                continue
            if interp and ch == '{':
                self.blank(seg, j + 1)
                j = self.code(j + 1, True)  # the code inside, with its own strings
                seg = j - 1  # the closing brace
                continue
            j += 1
        self.problems.append((i, 'unterminated string literal'))
        self.blank(seg, n)
        return n


def strip_comments_and_strings(src):
    """(stripped text, list of (position, problem), list of escaped-identifier positions)."""
    lx = Lexer(src)
    text = lx.run()
    return text, lx.problems, lx.escapes


def line_starts(text):
    starts = [0]
    for k, ch in enumerate(text):
        if ch == '\n':
            starts.append(k + 1)
    return starts


def line_of(starts, pos):
    lo, hi = 0, len(starts) - 1
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if starts[mid] <= pos:
            lo = mid
        else:
            hi = mid - 1
    return lo + 1


def attribute_spans(text):
    """(start, end) of the contents of each @[...] and attribute [...] list."""
    spans = []
    for m in re.finditer(r"@\[|(?<![\w'!?.])attribute\s*\[", text):
        start = m.end()
        depth, k = 1, start
        while k < len(text) and depth:
            if text[k] == '[':
                depth += 1
            elif text[k] == ']':
                depth -= 1
            k += 1
        spans.append((start, k - 1 if depth == 0 else k))
    return spans


def tokens(text):
    """(position, token, after a dot) for each identifier or `#` command, by Lean's identifier rules."""
    n = len(text)
    k = 0
    while k < n:
        c = text[k]
        if is_id_first(c) or (c == '#' and k + 1 < n and is_id_first(text[k + 1])):
            start = k
            k += 1
            while k < n and is_id_rest(text[k]):
                k += 1
            while k + 1 < n and text[k] == '.' and is_id_first(text[k + 1]):
                k += 1
                while k < n and is_id_rest(text[k]):
                    k += 1
            yield start, text[start:k], start > 0 and text[start - 1] == '.'
            continue
        if '0' <= c <= '9':
            while k < n and '0' <= text[k] <= '9':
                k += 1
            continue
        k += 1


def is_command(tok):
    if tok.startswith('#'):
        return tok not in HASH_ALLOWED
    if '.' in tok:
        return False
    return tok in COMMANDS or tok.startswith(COMMAND_PREFIXES)


def is_attr(name):
    return name in ATTRS or name.startswith(ATTR_PREFIXES) or name.endswith(ATTR_SUFFIXES)


def token_hits(text, hit, level):
    spans = attribute_spans(text)

    def in_span(pos):
        for a, b in spans:
            if a <= pos < b:
                return True
        return False

    for pos, tok, after_dot in tokens(text):
        comps = tok.lstrip('#').split('.')
        if in_span(pos):
            for name in [tok] + comps:
                if is_attr(name):
                    hit(pos, 'attribute:' + name, level)
                    break
        elif not after_dot and is_command(tok):
            hit(pos, 'command:' + tok, level)
        for comp in comps:
            if comp in WORDS or comp.startswith('unsafe'):
                hit(pos, 'word:' + comp, level)


def scan_lean(src):
    """Return (hits, notes) for one Lean source text."""
    stripped, problems, escapes = strip_comments_and_strings(src)
    starts = line_starts(src)
    lines = src.split('\n')
    hits = []
    seen = set()
    notes = []

    def hit(pos, kind, level):
        ln = line_of(starts, pos)
        if (ln, kind) in seen:
            return
        seen.add((ln, kind))
        hits.append({'line': ln, 'kind': kind, 'level': level, 'text': lines[ln - 1].strip()[:200]})

    for pos, what in problems:
        hit(pos, 'lexer:' + what, 'likely')
    for pos in escapes:
        hit(pos, 'escaped-identifier', 'likely')
    token_hits(stripped, hit, 'likely')
    # The raw text, comments and strings included: what the lexer above may have misread.
    for k, ch in enumerate(src):
        if ch == '«':
            hit(k, 'escaped-identifier', 'possible')
    token_hits(src.replace('«', ' ').replace('»', ' '), hit, 'possible')
    for m in IMPORT_RE.finditer(stripped):
        mod = m.group(1)
        if mod == 'Lean' or mod.startswith('Lean.'):
            notes.append('line %d: imports %s (a note, not a hit: Mathlib re-exports Lean)'
                         % (line_of(starts, m.start()), mod))
    hits.sort(key=lambda h: (h['line'], h['level'] != 'likely', h['kind']))
    return hits, notes


def parse_raw_diff(raw):
    """Entries of `git diff-tree -r -z --raw`: dicts with status, old_mode, new_mode, blob, paths."""
    parts = raw.split(b'\0')
    entries = []
    k = 0
    while k < len(parts):
        head = parts[k]
        if not head:
            k += 1
            continue
        if not head.startswith(b':'):
            raise GitError('unexpected diff-tree output: %r' % head[:80])
        fields = head[1:].decode('ascii').split()
        old_mode, new_mode, _old_sha, new_sha, status = fields[:5]
        npaths = 2 if status[:1] in ('R', 'C') else 1
        paths = [p.decode('utf-8', 'surrogateescape') for p in parts[k + 1:k + 1 + npaths]]
        k += 1 + npaths
        entries.append({'status': status, 'old_mode': old_mode, 'new_mode': new_mode, 'blob': new_sha,
                        'paths': paths})
    return entries


STATUS_WORDS = {'M': 'modifies', 'D': 'deletes', 'R': 'renames', 'C': 'copies', 'T': 'changes the type of',
                'U': 'leaves unmerged', 'X': 'changes'}
MODE_WORDS = {'120000': 'a symlink', '160000': 'a submodule', '100755': 'an executable file'}


def is_text_name(name):
    stem, dot, ext = name.partition('.')
    return stem.upper() in TEXT_STEMS or ('.' + name.rsplit('.', 1)[-1].lower() in TEXT_EXTS and dot != '')


def folded(paths):
    """Casefolded files and casefolded directories (every proper prefix) of the given paths."""
    files, dirs = set(), set()
    for p in paths:
        parts = p.casefold().split('/')
        files.add('/'.join(parts))
        for d in range(1, len(parts)):
            dirs.add('/'.join(parts[:d]))
    return files, dirs


def clashes(path, files, dirs):
    parts = path.casefold().split('/')
    cf = '/'.join(parts)
    return cf in files or cf in dirs or any('/'.join(parts[:d]) in files for d in range(1, len(parts)))


def scan(base, head, repo=None):
    base_sha = git(repo, 'rev-parse', '--verify', base + '^{commit}').decode().strip()
    head_sha = git(repo, 'rev-parse', '--verify', head + '^{commit}').decode().strip()
    mb = git(repo, 'merge-base', base_sha, head_sha).decode().strip()
    raw = git(repo, 'diff-tree', '-r', '-z', '-M', '--no-abbrev', '--no-commit-id', mb, head_sha)
    entries = parse_raw_diff(raw)
    base_files = set(p for p in git(repo, 'ls-tree', '-r', '-z', '--full-tree', '--name-only', base_sha, '--',
                                    PREFIX).decode('utf-8', 'surrogateescape').split('\0') if p)
    base_cf, base_cf_dirs = folded(base_files)
    added = []
    problems = []
    files = []
    n_lean = 0
    for e in entries:
        odd = [p for p in e['paths'] if has_control(p)]
        if odd:
            problems.append('changes a path with a control character or invalid UTF-8: %s'
                            % ', '.join(ascii(p) for p in odd))
            continue
        st = e['status'][:1]
        if st != 'A':
            what = STATUS_WORDS.get(st, 'changes')
            problems.append('%s %s' % (what, ' -> '.join(e['paths'])))
            continue
        path = e['paths'][0]
        mode = e['new_mode']
        if not path.startswith(PREFIX):
            problems.append('adds %s, outside %s' % (path, PREFIX))
            continue
        if mode != '100644':
            problems.append('adds %s as %s' % (path, MODE_WORDS.get(mode, 'mode ' + mode)))
            continue
        if clashes(path, base_cf, base_cf_dirs):
            problems.append('adds %s, which clashes with a path that already exists in BASE (compared without '
                            'case)' % path)
            continue
        if clashes(path, *folded(added)):
            problems.append('adds %s, which clashes with another added path when compared without case' % path)
            continue
        added.append(path)
        data = git(repo, 'cat-file', 'blob', e['blob'])
        entry = {'path': path, 'bytes': len(data), 'hits': [], 'notes': [], 'blob': e['blob'], 'mode': mode}
        if path.endswith('.lean'):
            if not LEAN_PATH_RE.match(path):
                problems.append('adds %s, which is not a plain module path (ASCII letters, digits and '
                                'underscores in each component)' % path)
                continue
            entry['type'] = 'lean'
            n_lean += 1
            try:
                src = data.decode('utf-8')
            except UnicodeDecodeError:
                src = data.decode('utf-8', 'replace')
                entry['notes'].append('not valid UTF-8')
            hits, notes = scan_lean(src)
            entry['hits'] = hits
            entry['notes'] += notes
        else:
            m = TEXT_PATH_RE.match(path)
            if not m or not is_text_name(m.group(1)):
                problems.append('adds %s, which is neither a Lean file nor a plain-text file (LICENSE, NOTICE, '
                                'README.md, ...) in a helper directory' % path)
                continue
            if b'\0' in data:
                problems.append('adds %s, which is not plain text' % path)
                continue
            try:
                data.decode('utf-8')
            except UnicodeDecodeError:
                problems.append('adds %s, which is not plain text' % path)
                continue
            entry['type'] = 'text'
            entry['notes'].append('plain-text file: passes the gate, listed for the reader')
        if entry['bytes'] > MAX_BYTES:
            entry['notes'].append('over 150 KB (%d bytes)' % entry['bytes'])
        files.append(entry)
    if not entries:
        problems.append('the pull request changes nothing')
    elif n_lean == 0 and not problems:
        problems.append('adds no Lean file under %s' % PREFIX)
    return {'base': base_sha, 'head': head_sha, 'merge_base': mb, 'scope_ok': not problems,
            'scope_problems': problems, 'files': files}


def summary(res):
    out = ['scan_contrib: base %s head %s merge base %s' % (res['base'], res['head'], res['merge_base'])]
    if res['scope_ok']:
        out.append('scope: ok, %d file(s) added under %s' % (len(res['files']), PREFIX))
    else:
        out.append('scope: OUT OF SCOPE for the automatic check')
        out += ['  ' + printable(p) for p in res['scope_problems']]
    for f in res['files']:
        likely = sum(1 for h in f['hits'] if h['level'] == 'likely')
        out.append('%s: %d bytes, %d likely hit(s), %d possible hit(s)'
                   % (f['path'], f['bytes'], likely, len(f['hits']) - likely))
        for h in f['hits']:
            out.append('  line %d %s %s: %s' % (h['line'], h['level'], h['kind'], printable(h['text'])))
        for note in f['notes']:
            out.append('  note: ' + note)
    out.append('The scan is advisory: a clean scan does not show that a file is safe.')
    return '\n'.join(out)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('base')
    ap.add_argument('head')
    ap.add_argument('--repo', default=None)
    ap.add_argument('--json', default=None, metavar='OUT')
    a = ap.parse_args(argv)
    try:
        res = scan(a.base, a.head, a.repo)
    except (GitError, OSError, ValueError) as ex:
        sys.stderr.write('scan_contrib: error: %s\n' % ex)
        return 1
    text = json.dumps(res, indent=2, ensure_ascii=False) + '\n'
    if a.json == '-':
        sys.stdout.write(text)
        sys.stderr.write(summary(res) + '\n')
    else:
        if a.json:
            with open(a.json, 'w', encoding='utf-8') as fh:
                fh.write(text)
        print(summary(res))
    return 0 if res['scope_ok'] else 2


if __name__ == '__main__':
    sys.exit(main())
