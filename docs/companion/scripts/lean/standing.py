#!/usr/bin/env python3
"""Mark the `assumed` declarations of a declaration index (decls.py) and write the final index.

A `def`/`abbrev` (or `structure`/`class`) of type `Prop` is a candidate hypothesis.  It is
`assumed` when it is
  - the type (or a constant in the type) of a binder of a headline theorem; or
  - a field of such a hypothesis structure, or the type of that field; or
  - for Deicyde/diophantine-z-q, named in a ```lean block or a "Bundle field" line of a row of
    docs/one-proof/OPEN.md.
Names are resolved in the index; a name the index lacks but the dependency index has is recorded
under `assumed_in_dependency`.  Every assumed row gets `assumed_by`.

Usage: python3 -I standing.py <fc dir> <raw index> <out json> --headline <name>[,<name>...]
       [--open <OPEN.md>] [--dep <raw dependency index>]
"""
import json
import os
import re
import sys

FC = sys.argv[1]
sys.path.insert(0, os.path.join(FC, 'scripts'))
from adapters import leanparse, leansnippets  # noqa: E402

raw, out = sys.argv[2:4]
opts = dict(zip(sys.argv[4::2], sys.argv[5::2]))
heads = opts['--headline'].split(',')
idx = json.load(open(raw, encoding='utf-8'))
rows = idx['declarations']
by_name = {}
for r in rows:
    by_name.setdefault(r['name'], []).append(r)
dep = None
if '--dep' in opts:
    dep = {}
    for r in json.load(open(opts['--dep'], encoding='utf-8'))['declarations']:
        dep.setdefault(r['name'], []).append(r)

IDENT = re.compile(r"(?<![\w.'])@?(_root_\.)?([A-Za-z_][\w'!?]*(?:\.[A-Za-z_][\w'!?]*)*)")


def opens_of(row):
    """Namespaces in scope at a row: its own namespace chain and the file's `open`s."""
    text = open(os.path.join(ROOT, row['file']), encoding='utf-8').read().split('\n')[:row['line']]
    opened = []
    for line in text:
        m = re.match(r'^\s*open\s+(?:scoped\s+)?([^\n]*?)(?:\s+in)?\s*$', line)
        if m:
            opened += [w for w in m.group(1).split() if re.match(r'^[A-Z][\w.]*$', w)]
    ns = row['name'].split('.')[:-1]
    chain = ['.'.join(ns[:k]) for k in range(len(ns), 0, -1)]
    return chain + opened + ['']


def resolve(ident, scope, table):
    """Full names in `table` that `ident` can denote from `scope`."""
    out = []
    for s in scope:
        cand = f'{s}.{ident}' if s else ident
        if cand in table:
            out.append(cand)
    if not out:
        out = [n for n in table if n.endswith('.' + ident)]
        if len(out) > 1:
            out = []
    return list(dict.fromkeys(out))


def binders(snippet):
    """The binder groups `( ... )`, `[ ... ]`, `{ ... }` of a theorem's statement before its final colon."""
    text = leanparse.strip_comments(snippet)
    lines = text.split('\n')
    ps = leansnippets.proof_start(lines, 0, len(lines))
    if ps:
        text = '\n'.join(lines[:ps[0]] + [lines[ps[0]][:ps[1]]])
    groups, depth, start = [], 0, None
    for i, ch in enumerate(text):
        if ch in '([{⦃':
            if depth == 0:
                start = i
            depth += 1
        elif ch in ')]}⦄':
            depth -= 1
            if depth == 0 and start is not None:
                groups.append(text[start + 1:i])
                start = None
        elif ch == ':' and depth == 0 and text[i:i + 2] != ':=' and start is None and groups:
            break
    return [g.split(':', 1)[1] for g in groups if ':' in g and not g.lstrip().startswith(('_ :=',))]


ROOT = opts.get('--root', '')

# an alias `abbrev P := Q` of a Prop `Q` (of this index or of the dependency) is a Prop too
ALIAS = re.compile(r'^(?:@\[[^\]]*\]\s*|\w+\s+)*?(?:def|abbrev)\s+\S+\s*:=\s*@?([A-Za-z_][\w\'.!?]*)\s*$')
for r in rows:
    if r['kind'] in ('def', 'abbrev') and not r['prop']:
        m = ALIAS.match(' '.join(leanparse.strip_comments(r['snippet']).split()))
        if m:
            scope = opens_of(r)
            tgt = [n for n in resolve(m.group(1).removeprefix('_root_.'), scope, by_name)
                   if any(x['prop'] for x in by_name[n])]
            dtgt = [n for n in resolve(m.group(1).removeprefix('_root_.'), scope, dep)
                    if any(x['prop'] for x in dep[n])] if dep is not None and not tgt else []
            if tgt or dtgt:
                r['prop'] = True
                r['alias_of'] = (tgt or ['dependency:' + dtgt[0]])[0]
assumed, dep_assumed, headline_report, missing = {}, {}, [], []


def mark(name, why, table_rows):
    for r in table_rows:
        if r['kind'] == 'field' or r['prop']:
            r.setdefault('assumed_by', [])
            if why not in r['assumed_by']:
                r['assumed_by'].append(why)
            r['standing'] = 'assumed'
    assumed.setdefault(name, []).append(why)


def mark_hyp(ident, scope, why, depth=0):
    names = resolve(ident, scope, by_name)
    props = [n for n in names if any(r['prop'] for r in by_name[n])]
    hit = []
    for n in props:
        mark(n, why, by_name[n])
        hit.append(n)
        for r in by_name[n]:
            if r.get('alias_of', '').startswith('dependency:'):
                dep_assumed.setdefault(r['alias_of'].split(':', 1)[1], []).append(why + ' (through ' + n + ')')
        # a hypothesis structure: its fields and their types are hypotheses too
        if depth == 0 and any(r['kind'] in ('structure', 'class') for r in by_name[n]):
            for f in [x for x in by_name if x.startswith(n + '.') and x.count('.') == n.count('.') + 1]:
                frows = by_name[f]
                if any(r['kind'] == 'field' for r in frows):
                    mark(f, why + ' (field of ' + n + ')', [r for r in frows if r['kind'] == 'field'])
                    sn = frows[0]['snippet']
                    ty = sn.split(':', 1)[1] if ':' in sn else ''
                    for m in IDENT.finditer(leanparse.strip_comments(ty)):
                        mark_hyp(m.group(2), opens_of(frows[0]), why + ' (type of ' + f + ')', 1)
    if not props and dep is not None:
        dn = [n for n in resolve(ident, scope, dep) if any(r['prop'] for r in dep[n])]
        for n in dn:
            dep_assumed.setdefault(n, []).append(why)
            hit.append('dependency:' + n)
    return hit


for h in heads:
    rs = by_name.get(h)
    if not rs:
        missing.append(h)
        continue
    r = rs[0]
    scope = opens_of(r)
    hyps = []
    for ty in binders(r['snippet']):
        for m in IDENT.finditer(ty):
            hyps += mark_hyp(m.group(2), scope, f'hypothesis of {h}')
    headline_report.append({'name': h, 'file': r['file'], 'line': r['line'], 'standing': r['standing'],
                            'hypotheses': list(dict.fromkeys(hyps))})

open_rows = []
if '--open' in opts:
    text = open(opts['--open'], encoding='utf-8').read()
    for sec in re.split(r'\n### ', text)[1:]:
        row = sec.split('\n', 1)[0].strip()
        names = re.findall(r'```lean\n(.*?)\n```', sec, flags=re.S)
        names = [n.strip() for block in names for n in block.split('\n') if n.strip()]
        names += re.findall(r'Bundle field `([^`]+)`', sec)
        names += re.findall(r'Argument `\w+` of `(\w+)`', sec) and []
        found = []
        for n in names:
            n = n.removeprefix('_root_.')
            if n in by_name:
                mark(n, f'open row {row} of docs/one-proof/OPEN.md', by_name[n])
                found.append(n)
            else:
                missing.append(f'OPEN.md row {row}: {n}')
        open_rows.append({'row': row, 'declarations': found})

counts = {}
for r in rows:
    counts[r['standing']] = counts.get(r['standing'], 0) + 1
idx.update({'headlines': headline_report, 'open_rows': open_rows, 'assumed_in_dependency': dep_assumed,
            'not_found': missing, 'standing_counts': counts,
            'candidate_hypotheses': sum(1 for r in rows if r['prop'])})
json.dump(idx, open(out, 'w', encoding='utf-8'), ensure_ascii=False)
print(json.dumps({'standing': counts, 'candidates': idx['candidate_hypotheses'],
                  'assumed names': len(assumed), 'dependency assumed': len(dep_assumed),
                  'not found': missing, 'headlines': [(h['name'], len(h['hypotheses'])) for h in headline_report]},
                 indent=0, ensure_ascii=False))
