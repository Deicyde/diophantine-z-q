"""Decide the discharge check from the trusted reporter's output; parse `#discharges` text for display only.

The verdict comes only from DischargesJson.lean (this directory, from BASE), run with `lake env lean` after
the build. It prints one line per theorem that discharges an open hypothesis of frozenTarget,

    DISCHARGE-JSON <nonce> {"theorem": str, "hits": [str], "assumes": [str], "assumes_open": [str],
      "axioms": [str], "sorry": bool}

(`assumes_open`: the open hypotheses its own hypotheses match) and finally `DISCHARGE-JSON <nonce> {"summary": {"open_hypotheses": N, "theorems_checked": M,
"discharging": K}}`. Only lines that start with `DISCHARGE-JSON ` and this run's nonce count; every other
line is ignored. A counted line whose JSON or field types are wrong, or whose names hold a control character,
is rejected, and a rejected line fails the check. A hit that is also in `assumes_open` proves nothing (the
theorem assumes what it proves), so it does not count. The build log is read for errors and for Lean's sorry
warning on the added files (Lean 4.35 writes "declaration uses `sorry`").

The text output of `#discharges` (`DISCHARGES [...] by <theorem>`, `still assumes: [...]`, `axioms: [...]`)
is parsed for display only and never decides anything: a theorem name can hold a line break.

Usage:
  python3 discharges_log.py LOG
      parse `#discharges` text and print it as JSON (display only).
  python3 discharges_log.py LOG --nonce N
      parse the reporter's lines and print them as JSON.
  python3 discharges_log.py LOG --nonce N --result OUT --manifest M --build-log B --build-status N
      [--lean-status N] [--text-log T] [--render-status N] [--seconds S] [--build-seconds S] [--time-file F]
      write the check's result.json to OUT, print the verdict, exit 0 on pass and 1 on fail.
      An absent --lean-status means the reporter did not run. --render-status is information only.
  python3 discharges_log.py --measure DIR --result OUT --build-status N [--seconds S] [--commit SHA]
      write the measurement's result.json from DIR (build.log, time.txt, df-before.txt, df-after.txt,
      free-before.txt, free-after.txt).
"""
import argparse
import json
import re
import sys
import unicodedata

STANDARD_AXIOMS = ('propext', 'Classical.choice', 'Quot.sound')
TAG = 'DISCHARGE-JSON'
RECORD_KEYS = {'theorem', 'hits', 'assumes', 'assumes_open', 'axioms', 'sorry'}
SUMMARY_KEYS = ('open_hypotheses', 'theorems_checked', 'discharging')
NONCE_RE = re.compile(r'[A-Za-z0-9]+\Z')
SORRY_RE = re.compile(r"declaration uses [`']sorry[`']")
ERROR_RE = re.compile(r'(?::\d+:\d+: error\b|^error\b)')
# Text output of #discharges, for display only.
RECORD_RE = re.compile(r'(?:^|:\s)\s*DISCHARGES \[(.*?)\] by (.+?)( \(uses sorry: not a proof\))?\s*$')
SUMMARY_RE = re.compile(r'#discharges: (\d+) open hypotheses, (\d+) theorems checked, (\d+) discharge one')
OPEN_BR = '([{⟨'
CLOSE_BR = ')]}⟩'
# Binder notations whose binder list ends with a comma (∀ x, P x).
BINDERS = '∀∃ΠΣ⨆⨅⋃⋂∑∏∫∮∐⨁⨂'


def lines_of(text):
    """Lines split at newlines only (str.splitlines also splits at other separators)."""
    return [ln[:-1] if ln.endswith('\r') else ln for ln in text.split('\n')]


def has_control(s, allow=''):
    return any(c not in allow and unicodedata.category(c) in ('Cc', 'Cf', 'Zl', 'Zp', 'Cs') for c in s)


def is_int(x):
    return isinstance(x, int) and not isinstance(x, bool)


def _no_duplicates(pairs):
    out = {}
    for k, v in pairs:
        if k in out:
            raise ValueError('duplicate key %r' % k)
        out[k] = v
    return out


def check_record(obj):
    """None if obj is a well-formed record, else why not."""
    if set(obj) != RECORD_KEYS:
        return 'the record has keys %s' % sorted(obj)
    t = obj['theorem']
    if not isinstance(t, str) or not t:
        return 'the theorem name is not a non-empty string'
    if has_control(t):
        return 'the theorem name %s contains a control character' % json.dumps(t)
    for key in ('hits', 'axioms', 'assumes_open'):
        v = obj[key]
        if not isinstance(v, list) or not all(isinstance(x, str) and x and not has_control(x) for x in v):
            return '%s of %s is not a list of plain names' % (key, json.dumps(t))
    if not obj['hits']:
        return 'the record for %s has no hits' % json.dumps(t)
    a = obj['assumes']
    if not isinstance(a, list) or not all(isinstance(x, str) and not has_control(x, '\n') for x in a):
        return 'assumes of %s is not a list of strings' % json.dumps(t)
    if not isinstance(obj['sorry'], bool):
        return 'sorry of %s is not true or false' % json.dumps(t)
    return None


def parse_json(text, nonce):
    """Parse the reporter's lines that carry `nonce`. Returns {discharges, summary, rejected}."""
    prefix = '%s %s ' % (TAG, nonce)
    discharges, rejected = [], []
    summary = None
    for n, line in enumerate(lines_of(text), 1):
        if not line.startswith(prefix):
            continue
        try:
            obj = json.loads(line[len(prefix):], object_pairs_hook=_no_duplicates)
        except ValueError as ex:
            rejected.append('line %d: not one JSON object (%s)' % (n, ex))
            continue
        if not isinstance(obj, dict):
            rejected.append('line %d: not a JSON object' % n)
            continue
        if 'summary' in obj:
            s = obj['summary']
            if set(obj) != {'summary'} or not isinstance(s, dict) or set(s) != set(SUMMARY_KEYS) \
                    or not all(is_int(s[k]) and s[k] >= 0 for k in SUMMARY_KEYS):
                rejected.append('line %d: a malformed summary' % n)
            elif summary is not None:
                rejected.append('line %d: a second summary' % n)
            else:
                summary = {k: s[k] for k in SUMMARY_KEYS}
            continue
        why = check_record(obj)
        if why:
            rejected.append('line %d: %s' % (n, why))
            continue
        uses_sorry = obj['sorry'] or 'sorryAx' in obj['axioms']
        nonstandard = [a for a in obj['axioms'] if a not in STANDARD_AXIOMS and a != 'sorryAx']
        proved = [h for h in obj['hits'] if h not in obj['assumes_open']]
        discharges.append({'theorem': obj['theorem'], 'hypotheses': obj['hits'], 'still_assumes': obj['assumes'],
                           'proved': proved, 'axioms': obj['axioms'], 'uses_sorry': uses_sorry,
                           'nonstandard_axioms': nonstandard, 'clean': not uses_sorry and not nonstandard})
    return {'discharges': discharges, 'summary': summary, 'rejected': rejected}


def balanced(s):
    depth = 0
    for ch in s:
        if ch in OPEN_BR:
            depth += 1
        elif ch in CLOSE_BR:
            depth -= 1
    return depth <= 0


def split_list(text):
    """'[a, f (b, c), d]' -> ['a', 'f (b, c)', 'd'], splitting only at top-level commas."""
    s = ' '.join(text.split())
    if s.startswith('[') and s.endswith(']'):
        s = s[1:-1]
    items, depth, cur = [], 0, []
    binders = 0  # top-level binders (∀ x, ...) still waiting for their comma
    for ch in s:
        if ch in OPEN_BR:
            depth += 1
        elif ch in CLOSE_BR:
            depth -= 1
        elif ch in BINDERS and depth == 0:
            binders += 1
        if ch == ',' and depth == 0 and binders:
            binders -= 1
            cur.append(ch)
        elif ch == ',' and depth == 0:
            items.append(''.join(cur).strip())
            cur = []
        else:
            cur.append(ch)
    last = ''.join(cur).strip()
    if last or items:
        items.append(last)
    return [i for i in items if i]


def parse_text(text):
    """Parse `#discharges` text output, for display only. Returns {discharges, summary}."""
    discharges = []
    summary = None
    cur = None
    field = None
    buf = ''

    def finish():
        cur[field] = split_list(buf)

    for raw in lines_of(text):
        line = raw.rstrip()
        if field is not None:
            buf += ' ' + line.strip()
            if balanced(buf):
                finish()
                field = None
            continue
        m = RECORD_RE.search(line)
        if m:
            cur = {'hypotheses': split_list(m.group(1)), 'theorem': m.group(2).strip(),
                   'uses_sorry': bool(m.group(3)), 'still_assumes': [], 'axioms': []}
            discharges.append(cur)
            continue
        m = SUMMARY_RE.search(line)
        if m:
            summary = {'open_hypotheses': int(m.group(1)), 'theorems_checked': int(m.group(2)),
                       'discharging': int(m.group(3))}
            cur = None
            continue
        s = line.strip()
        if cur is not None and (s.startswith('still assumes:') or s.startswith('axioms:')):
            field = 'still_assumes' if s.startswith('still') else 'axioms'
            buf = s.split(':', 1)[1].strip()
            if not buf.startswith('[') or balanced(buf):
                finish()
                field = None
    if field is not None:
        finish()
    for d in discharges:
        d['uses_sorry'] = d['uses_sorry'] or 'sorryAx' in d['axioms']
    return {'discharges': discharges, 'summary': summary}


def error_lines(log):
    return [ln.strip() for ln in lines_of(log) if ERROR_RE.search(ln)]


def lake_jobs(build_log):
    """The Lake job count, if the build output shows it."""
    m = None
    for m in re.finditer(r'Build completed successfully \((\d+) jobs?\)', build_log):
        pass
    if m:
        return int(m.group(1))
    totals = [int(t) for t in re.findall(r'\[\d+/(\d+)\]', build_log)]
    return max(totals) if totals else None


def peak_kib(time_text):
    """Peak resident memory in KiB from GNU time -v output, if present."""
    m = re.search(r'Maximum resident set size \(kbytes\): (\d+)', time_text)
    return int(m.group(1)) if m else None


def sorry_warnings(build_log, added):
    """Build-log lines saying a declaration in an added file uses sorry (Lake or Lean message form)."""
    return [ln.strip() for ln in lines_of(build_log) if SORRY_RE.search(ln) and any(p in ln for p in added)]


def evaluate(parsed, build_status=0, lean_status=0, build_log='', added=(), lean_log=''):
    """The verdict from the reporter's parsed lines: (passed, reasons)."""
    reasons = []
    if build_status != 0:
        reasons.append('the build failed (lake build exit status %d)' % build_status)
    errs = error_lines(build_log)
    if errs:
        reasons.append('the build log reports %d error(s)' % len(errs))
    for line in sorry_warnings(build_log, added):
        reasons.append('the build reports sorry in an added file: %s' % line)
    ran = build_status == 0 and lean_status is not None
    if build_status == 0 and lean_status is None:
        reasons.append('the reporter did not run')
    if lean_status not in (None, 0):
        reasons.append('the reporter run failed (exit status %d)' % lean_status)
    errs = error_lines(lean_log)
    if errs:
        reasons.append('the reporter run reported %d error(s)' % len(errs))
    for r in parsed['rejected']:
        reasons.append('a reporter line was rejected: %s' % r)
    if ran and lean_status == 0 and parsed['summary'] is None:
        reasons.append('the reporter printed no summary line')
    s = parsed['summary']
    if s is not None and s['discharging'] != len(parsed['discharges']):
        reasons.append('the reporter summary counts %d discharging theorems but printed %d records'
                       % (s['discharging'], len(parsed['discharges'])))
    for d in parsed['discharges']:
        if not d['proved']:
            reasons.append('%s assumes the hypothesis it proves' % d['theorem'])
        if d['uses_sorry']:
            reasons.append('%s uses sorry' % d['theorem'])
        if d['nonstandard_axioms']:
            reasons.append('%s uses axioms beyond propext, Classical.choice and Quot.sound: %s'
                           % (d['theorem'], ', '.join(d['nonstandard_axioms'])))
    if ran and not any(d['clean'] and d['proved'] for d in parsed['discharges']):
        reasons.append('no theorem discharges an open hypothesis')
    return not reasons, reasons


def read(path):
    if not path:
        return ''
    try:
        with open(path, encoding='utf-8', errors='replace') as fh:
            return fh.read()
    except FileNotFoundError:
        return ''


def write_json(path, obj):
    with open(path, 'w', encoding='utf-8') as fh:
        json.dump(obj, fh, indent=2, ensure_ascii=False)
        fh.write('\n')


def measure_result(d, build_status, seconds, commit):
    def f(name):
        return read('%s/%s' % (d, name))
    build_log = f('build.log')
    time_text = f('time.txt')
    return {
        'kind': 'measure', 'commit': commit, 'target': '+ZInQKernel.OneProof.Main',
        'build': {'status': build_status, 'timed_out': build_status == 124, 'seconds': seconds,
                  'lake_jobs': lake_jobs(build_log), 'peak_kib': peak_kib(time_text)},
        'time_v': time_text.strip() or None,
        'disk_before': f('df-before.txt').strip(), 'disk_after': f('df-after.txt').strip(),
        'memory_before': f('free-before.txt').strip(), 'memory_after': f('free-after.txt').strip(),
    }


def main(argv=None):
    ap = argparse.ArgumentParser(description='Decide the discharge check from the reporter output.')
    ap.add_argument('log', nargs='?')
    ap.add_argument('--nonce')
    ap.add_argument('--result')
    ap.add_argument('--manifest')
    ap.add_argument('--build-log')
    ap.add_argument('--text-log')
    ap.add_argument('--time-file')
    ap.add_argument('--build-status', type=int, default=0)
    ap.add_argument('--lean-status', type=int, default=None)
    ap.add_argument('--render-status', type=int, default=None)
    ap.add_argument('--seconds', type=int, default=None)
    ap.add_argument('--build-seconds', type=int, default=None)
    ap.add_argument('--measure', metavar='DIR')
    ap.add_argument('--commit')
    a = ap.parse_args(argv)
    if a.measure:
        if not a.result:
            ap.error('--measure needs --result')
        res = measure_result(a.measure, a.build_status, a.seconds, a.commit)
        write_json(a.result, res)
        b = res['build']
        print('measurement: build exit status %d, %s s, %s Lake jobs, peak %s KiB'
              % (b['status'], b['seconds'], b['lake_jobs'], b['peak_kib']))
        return 0
    if not a.log:
        ap.error('LOG is required')
    if a.nonce is None:
        if a.result:
            ap.error('--result needs --nonce: the verdict comes only from the reporter lines')
        print(json.dumps(parse_text(read(a.log)), indent=2, ensure_ascii=False))
        return 0
    if not NONCE_RE.match(a.nonce):
        ap.error('--nonce must be ASCII letters and digits')
    lean_log = read(a.log)
    parsed = parse_json(lean_log, a.nonce)
    if not a.result:
        print(json.dumps(parsed, indent=2, ensure_ascii=False))
        return 0
    manifest = json.loads(read(a.manifest) or '{}')
    added = manifest.get('added', [])
    build_log = read(a.build_log)
    passed, reasons = evaluate(parsed, a.build_status, a.lean_status, build_log, added, lean_log)
    result = {
        'kind': 'check',
        'base': manifest.get('base'), 'head': manifest.get('head'), 'pr': manifest.get('pr'),
        'added': added,
        'modules': [p[:-5].replace('/', '.') for p in added if p.endswith('.lean')],
        'passed': passed, 'reasons': reasons,
        'discharges': parsed['discharges'], 'summary': parsed['summary'], 'rejected': parsed['rejected'],
        'text_discharges': parse_text(read(a.text_log))['discharges'] if a.text_log else [],
        'build': {'status': a.build_status, 'seconds': a.build_seconds, 'lake_jobs': lake_jobs(build_log),
                  'peak_kib': peak_kib(read(a.time_file))},
        'lean_status': a.lean_status, 'render_status': a.render_status, 'seconds': a.seconds,
    }
    write_json(a.result, result)
    print('discharge check: %s (advisory: contributor code ran on this runner before this verdict)'
          % ('pass' if passed else 'fail'))
    for r in reasons:
        print('  ' + r)
    return 0 if passed else 1


if __name__ == '__main__':
    sys.exit(main())
