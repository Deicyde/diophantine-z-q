"""Format the job summary of the discharge check.

Usage: python3 discharge_comment.py --scan SCAN.json [--result RESULT.json] [--pr N] [--run-url URL]
       [--out FILE]

SCAN.json is scan_contrib.py's output for the pull request, written by the scope step before anything is built;
RESULT.json is the check's .sandbox/out/result.json (absent when the pull request is out of scope, or when the
run wrote none). The base and head come from SCAN.json, never from RESULT.json. A RESULT.json that does not have
the expected shape counts as no result. Every piece of text from the pull request or the run is printed inside a
code span. Prints the summary as Markdown (the workflow appends it to $GITHUB_STEP_SUMMARY), or writes it to
FILE.
"""
import argparse
import json
import re
import sys

PREFIX = 'ZInQKernel/Contrib/OneProof/'
HIT_SENTENCE = ('This file has scan hits: it may contain code that runs at build time. A file with scan hits is '
                'not merged, and this result does not count while it has them.')
ADVISORY = ('The result is advisory for every file: contributor code runs during the build, and again when the '
            'reporter imports it, so it can forge the result, and a clean scan does not rule that out.')
REMINDER = 'The project\'s agents also run the build, axiom and build-time-code checks before a merge; this check is one of them.'
MAX_HITS = 50


def code(s):
    """s as one inline code span, fenced by a backtick run longer than any run inside it."""
    s = ' '.join(str(s).split())
    if not s:
        return '(empty)'
    longest = max((len(r) for r in re.findall('`+', s)), default=0)
    fence = '`' * (longest + 1)
    if longest:
        return '%s %s %s' % (fence, s, fence)
    return fence + s + fence


def short(sha):
    return code(sha[:12]) if isinstance(sha, str) and sha else 'unknown'


def is_int(x):
    return isinstance(x, int) and not isinstance(x, bool)


def is_strs(x):
    return isinstance(x, list) and all(isinstance(i, str) for i in x)


def check_records(ds, name):
    if not isinstance(ds, list):
        return '%s is not a list' % name
    for k, d in enumerate(ds):
        where = '%s[%d]' % (name, k)
        if not isinstance(d, dict):
            return '%s is not an object' % where
        if not isinstance(d.get('theorem'), str):
            return '%s.theorem is not a string' % where
        for key in ('hypotheses', 'still_assumes', 'axioms'):
            if not is_strs(d.get(key)):
                return '%s.%s is not a list of strings' % (where, key)
        if not isinstance(d.get('uses_sorry'), bool):
            return '%s.uses_sorry is not true or false' % where
        if 'proved' in d and not is_strs(d['proved']):
            return '%s.proved is not a list of strings' % where
    return None


def validate(result):
    """None if result.json has the expected shape, else where it does not."""
    if not isinstance(result, dict):
        return 'not a JSON object'
    if result.get('kind') != 'check':
        return 'kind is not "check"'
    if not isinstance(result.get('passed'), bool):
        return 'passed is not true or false'
    if not is_strs(result.get('reasons')):
        return 'reasons is not a list of strings'
    for key in ('base', 'head'):
        if result.get(key) is not None and not isinstance(result.get(key), str):
            return '%s is not a string' % key
    why = check_records(result.get('discharges'), 'discharges') or \
        check_records(result.get('text_discharges', []), 'text_discharges')
    if why:
        return why
    s = result.get('summary')
    if s is not None and not (isinstance(s, dict) and all(
            is_int(s.get(k)) for k in ('open_hypotheses', 'theorems_checked', 'discharging'))):
        return 'summary is malformed'
    b = result.get('build')
    if not isinstance(b, dict):
        return 'build is not an object'
    for key in ('status', 'seconds', 'lake_jobs', 'peak_kib'):
        if b.get(key) is not None and not is_int(b.get(key)):
            return 'build.%s is not a number' % key
    for key in ('seconds', 'render_status', 'lean_status'):
        if result.get(key) is not None and not is_int(result.get(key)):
            return '%s is not a number' % key
    if not is_strs(result.get('rejected', [])):
        return 'rejected is not a list of strings'
    return None


def write_records(w, ds):
    for d in ds:
        proved = d.get('proved')
        hyps = ', '.join(code(h) + (' (assumed, so not proved)' if proved is not None and h not in proved else '')
                         for h in d['hypotheses'])
        flag = ' (uses sorry: not a proof)' if d['uses_sorry'] else ''
        w('- DISCHARGES %s by %s%s' % (hyps, code(d['theorem']), flag))
        assumes = d['still_assumes']
        w('  - still assumes: %s' % ('; '.join(code(a) for a in assumes) if assumes else 'nothing'))
        w('  - axioms: %s' % (', '.join(code(a) for a in d['axioms']) or 'none'))
    w('')


def format_comment(scan, result=None, run_url=None, pr=None):
    out = []
    w = out.append
    in_scope = bool(scan.get('scope_ok'))
    files = scan.get('files', [])
    flagged = [f for f in files if f.get('hits')]
    invalid = None
    if in_scope and result is not None:
        invalid = validate(result)
    if not in_scope:
        verdict = 'out of scope'
    elif result is None or invalid:
        verdict = 'no result'
    else:
        verdict = 'pass' if result['passed'] else 'fail'
    if in_scope and flagged:
        w('### Discharge check: %s, which does not count while a file has scan hits'
          % verdict)
    else:
        w('### Discharge check: %s' % verdict)
    w('')
    line = 'Base %s, head %s' % (short(scan.get('base')), short(scan.get('head')))
    if pr is not None:
        line += ', pull request #%d' % pr
    w(line + '.')
    if run_url:
        w('Run: %s' % run_url)
    w('')
    if not in_scope:
        w('The automatic check covers only pull requests that add new files under %s and change nothing '
          'else. This pull request is out of scope, so nothing was built:' % code(PREFIX))
        w('')
        for p in scan.get('scope_problems', []):
            w('- %s' % code(p))
        w('')
    elif result is None:
        w('The check wrote no result; the run log says why.')
        w('')
    elif invalid:
        w('The result does not have the expected shape (%s), so it counts as no result.' % invalid)
        w('')
    else:
        if result.get('head') != scan.get('head') or result.get('base') != scan.get('base'):
            w('**The result is for base %s and head %s, not the scanned pair; it does not count.**'
              % (short(result.get('base')), short(result.get('head'))))
            w('')
        if result['passed']:
            w('**Pass:** at least one theorem discharges an open hypothesis, and every reported theorem proves a '
              'hypothesis it does not assume, uses no `sorry`, and uses only the axioms `propext`, '
              '`Classical.choice` and `Quot.sound`.')
        else:
            w('**Fail:**')
            w('')
            for r in result['reasons']:
                w('- %s' % code(r))
        w('')
        ds = result['discharges']
        text_ds = result.get('text_discharges', [])
        if ds:
            w('What the reporter finds:')
            w('')
            write_records(w, ds)
        elif text_ds:
            w('The text output of `#discharges`, for display only (it does not decide the result):')
            w('')
            write_records(w, text_ds)
        s = result.get('summary')
        if s:
            w('Reporter summary: %d open hypotheses, %d theorems checked, %d discharge one.'
              % (s['open_hypotheses'], s['theorems_checked'], s['discharging']))
            w('')
        b = result['build']
        stats = []
        if b.get('lake_jobs') is not None:
            stats.append('%d Lake jobs' % b['lake_jobs'])
        if b.get('seconds') is not None:
            stats.append('build %d s' % b['seconds'])
        if b.get('peak_kib') is not None:
            stats.append('peak memory %d MiB' % (b['peak_kib'] // 1024))
        if result.get('seconds') is not None:
            stats.append('whole check %d s wall-clock' % result['seconds'])
        if stats:
            w('Build: %s.' % ', '.join(stats))
            w('')
        if result.get('render_status') not in (None, 0):
            w('`render_open.py --check` reports that the base commit\'s generated documents are out of date. '
              'This is information for the maintainers only; it does not depend on this pull request.')
            w('')
    if files:
        w('Scan for build-time code (advisory, on the git objects, before anything was built; "likely" hits '
          'are outside comments and strings, "possible" hits are anywhere in the text):')
        w('')
        if not flagged:
            w('- no hits in %s.' % ', '.join(code(f.get('path', '')) for f in files))
        for f in flagged:
            w('- %s: %s' % (code(f.get('path', '')), HIT_SENTENCE))
            for h in f['hits'][:MAX_HITS]:
                w('  - line %s, %s, %s: %s' % (code(h.get('line')), code(h.get('level', 'likely')),
                                               code(h.get('kind')), code(h.get('text'))))
            if len(f['hits']) > MAX_HITS:
                w('  - and %d more' % (len(f['hits']) - MAX_HITS))
        for f in files:
            for n in f.get('notes', []):
                w('- note on %s: %s' % (code(f.get('path', '')), code(n)))
        w('')
    w(ADVISORY)
    w(REMINDER)
    return '\n'.join(out) + '\n'


def main(argv=None):
    ap = argparse.ArgumentParser(description='Format the discharge check job summary.')
    ap.add_argument('--scan', required=True)
    ap.add_argument('--result')
    ap.add_argument('--pr', type=int)
    ap.add_argument('--run-url')
    ap.add_argument('--out')
    a = ap.parse_args(argv)
    with open(a.scan, encoding='utf-8') as fh:
        scan = json.load(fh)
    result = None
    if a.result:
        try:
            with open(a.result, encoding='utf-8') as fh:
                result = json.load(fh)
        except FileNotFoundError:
            result = None
        except ValueError:
            result = 'not valid JSON'
    text = format_comment(scan, result, a.run_url, a.pr)
    if a.out:
        with open(a.out, 'w', encoding='utf-8') as fh:
            fh.write(text)
    else:
        sys.stdout.write(text)
    return 0


if __name__ == '__main__':
    sys.exit(main())
