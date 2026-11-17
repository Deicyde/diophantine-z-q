"""Write docs/one-proof/frontier-crosswalk.tsv: the frontier IDs (H-n, T-n, Z-n) mapped to open hypotheses.

docs/research/frontier.md numbers every open statement on the path to `ZInQ.FrozenTarget` (H-n for the H part,
T-n for Tian-Yuan-Zhang, Z-n for Gross-Zagier), and claims on the upstream issues use those IDs. OPEN.md and
claims.tsv use the Lean field names of `ZInQ.OneProof.frozenTarget`. This script reads frontier.md at the
revisions in REVS (the ID of a row is kept across revisions) and matches each ID to an open hypothesis of
docs/one-proof/open-statements.json: by the field a row names, by the Lean constant it names, by the phrase
"field `x` of", or through the field-to-ID table rows ("| `field` (H-n; r6: H-m) | ...").

Usage, from the repository root: python3 scripts/one_proof/frontier_crosswalk.py [--check] [REV ...]
REV defaults to REVS (oldest first, so that IDs retired by a later revision still resolve); a revision missing
from the clone is skipped with a note. With --check, nothing is written: exit 1 if the file differs from what
the revisions give. Columns: id, field (empty when no open hypothesis matches), lean_name, revisions (the
revisions whose frontier.md has the ID), latest (yes when the last readable revision has it).
"""
import json, re, subprocess, sys

D = 'docs/one-proof/'
OUT = D + 'frontier-crosswalk.tsv'
# frontier.md revisions whose IDs appear in public claims and issues: the 11-13 refresh, r2, r3, r4, r5, r6, r7, r8, r9
REVS = ['249195fd0', 'f6df5fa32', 'cba8157f7', '5fd81e870', '085a7a53a', 'f18bcb904', '3691994d4', 'f96b7323d',
        '8342c2eb7', 'a6405dffb']
ROW = re.compile(r'^\|\s*([HTZ]-\d+)\s*\|([^|]*)\|(.*)$')
FIELD_ROW = re.compile(r'^\|\s*`([A-Za-z_][A-Za-z0-9_\']*)`\s*\(([^)]*)\)\s*\|')
ID = re.compile(r'\b([HTZ]-\d+)\b')
CODE = re.compile(r'`([^`]+)`')
FIELD_MENTION = re.compile(r'field `([A-Za-z_][A-Za-z0-9_\']*)` of ')


def head_constant(ty):
    """The constant a hypothesis type is about: the last binder body's head symbol."""
    body = ty.rsplit(',', 1)[-1] if ty.lstrip().startswith('∀') else ty
    tok = body.strip().split()[0] if body.strip() else ''
    return tok.strip('()')


def git(*args):
    r = subprocess.run(['git', *args], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None


def build(revs):
    hyps = json.load(open(D + 'open-statements.json'))['hypotheses']
    fields = {h['field'] for h in hyps}
    by_const = {}
    for h in hyps:
        c = head_constant(h['type'])
        if c:
            by_const[c] = h['field']

    def match(lean_name, text):
        if lean_name:
            for c, f in by_const.items():
                if c == lean_name or c.endswith('.' + lean_name):
                    return f
        for m in FIELD_MENTION.finditer(text):
            if m.group(1) in fields:
                return m.group(1)
        return ''

    rows, order, via_table, read = {}, [], {}, []
    for rev in revs:
        src = git('show', f'{rev}:docs/research/frontier.md')
        short = (git('rev-parse', '--short', rev) or '').strip()
        if src is None or not short:
            print(f'note: revision {rev} is not in this clone; skipped')
            continue
        read.append(short)
        for line in src.splitlines():
            t = FIELD_ROW.match(line)
            if t and t.group(1) in fields:
                for rid in ID.findall(t.group(2)):
                    via_table.setdefault(rid, t.group(1))
            m = ROW.match(line)
            if not m:
                continue
            rid, col2, rest = m.group(1), m.group(2), m.group(3)
            # older revisions write the column as `field : Lean.Name`, newer ones give the Lean name only
            named, lean = [], []
            for n in CODE.findall(col2):
                n = n.strip()
                m2 = re.match(r'^([A-Za-z_][A-Za-z0-9_\']*) : (.+)$', n)
                if m2:
                    named.append(m2.group(1))
                    lean.append(m2.group(2).strip())
                elif n in fields:
                    named.append(n)
                else:
                    lean.append(n)
            named = [n for n in named if n in fields]
            lean_name = lean[0] if lean else ''
            f = named[0] if named else match(lean_name, rest)
            r = rows.get(rid)
            if r is None:
                r = rows[rid] = {'id': rid, 'field': '', 'lean_name': '', 'revisions': []}
                order.append(rid)
            # a later revision's row wins: its names are the current ones
            r['lean_name'] = lean_name or r['lean_name']
            r['field'] = f or r['field']
            if short not in r['revisions']:
                r['revisions'].append(short)
    for rid, f in via_table.items():
        r = rows.get(rid)
        if r is None:
            r = rows[rid] = {'id': rid, 'field': '', 'lean_name': '', 'revisions': []}
            order.append(rid)
        r['field'] = r['field'] or f
    if not read:
        sys.exit('no frontier.md revision could be read')
    last = read[-1]
    key = lambda rid: ('HTZ'.index(rid[0]), int(rid[2:]))
    out = ['\t'.join(['id', 'field', 'lean_name', 'revisions', 'latest'])]
    for rid in sorted(order, key=key):
        r = rows[rid]
        out.append('\t'.join([rid, r['field'], r['lean_name'], ','.join(r['revisions']),
                              'yes' if last in r['revisions'] else 'no']))
    unmatched = sorted(fields - {r['field'] for r in rows.values()})
    return '\n'.join(out) + '\n', len(rows), sum(1 for r in rows.values() if r['field']), unmatched


def main(argv):
    check = '--check' in argv
    revs = [a for a in argv if a != '--check'] or REVS
    text, n, matched, unmatched = build(revs)
    if check:
        cur = open(OUT).read() if __import__('os').path.exists(OUT) else ''
        if cur != text:
            sys.exit(f'{OUT} is out of date: run python3 scripts/one_proof/frontier_crosswalk.py')
        print(f'ok: {OUT} is up to date ({n} IDs, {matched} matched)')
        return
    open(OUT, 'w').write(text)
    print(f'wrote {OUT}: {n} IDs, {matched} matched to an open hypothesis')
    if unmatched:
        print('open hypotheses with no frontier ID:', ', '.join(unmatched))


if __name__ == '__main__':
    main(sys.argv[1:])
