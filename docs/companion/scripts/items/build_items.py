#!/usr/bin/env python3
"""List the items of the manuscript: numbered statements, numbered displays, blueprint passages.

Usage: build_items.py <diophantine_zq.tex> <passages.json> <items.json> <items-text.json>

items.json holds numbers, names, labels, sections, nesting and line ranges only; the
statements' LaTeX goes to items-text.json, which is never committed.
"""
import json
import re
import sys

TEX, PASSAGES, OUT, TEXT = sys.argv[1:5]
src = open(TEX, encoding='utf-8').read().split('\n')
KINDS = {'theorem': 'Theorem', 'proposition': 'Proposition', 'lemma': 'Lemma',
         'corollary': 'Corollary', 'definition': 'Definition', 'remark': 'Remark'}
NUMBERED = r'equation|align|gather|multline|flalign|alignat'


def strip_comment(line):
    return re.sub(r'(?<!\\)%.*', '', line)


# ---- sections: the top-level section of every line --------------------------
section_of = [None] * (len(src) + 2)
sec, app, appendix, cur = 0, 0, False, 'front'
for i, line in enumerate(src, 1):
    l = strip_comment(line)
    if l.startswith('\\appendix'):
        appendix = True
    elif l.startswith('\\begin{thebibliography}'):
        cur = 'References'
    elif l.startswith('\\section*'):
        cur = re.match(r'\\section\*\{([^}]*)\}', l).group(1)
    elif l.startswith('\\section{'):
        if appendix:
            app += 1
            cur = chr(64 + app)
        else:
            sec += 1
            cur = str(sec)
    section_of[i] = cur

items = []
text = {}

# ---- numbered statements -----------------------------------------------------
counter = {}
open_stmt = None
for i, line in enumerate(src, 1):
    l = strip_comment(line)
    m = re.match(r'\\begin\{(' + '|'.join(KINDS) + r')\}', l)
    if m:
        s = section_of[i]
        counter[s] = counter.get(s, 0) + 1
        open_stmt = {'kind': m.group(1), 'number': f'{s}.{counter[s]}', 'start': i}
        continue
    m = re.match(r'\\end\{(' + '|'.join(KINDS) + r')\}', l)
    if m and open_stmt:
        a, b = open_stmt['start'], i
        labels = re.findall(r'\\label\{([^}]*)\}', '\n'.join(src[a - 1:min(b, a + 3)]))
        name = f"{KINDS[open_stmt['kind']]} {open_stmt['number']}"
        items.append({'id': name, 'kind': open_stmt['kind'], 'number': open_stmt['number'], 'name': None,
                      'label': labels[0] if labels else None, 'section': section_of[a], 'lines': [[a, b]]})
        text[name] = '\n'.join(src[a - 1:b])
        open_stmt = None

# ---- numbered displays -------------------------------------------------------
eqno = 0
envs = []        # (env, first line, last line)
stack = None
for i, line in enumerate(src, 1):
    l = strip_comment(line)
    for m in re.finditer(r'\\begin\{(' + NUMBERED + r')(\*?)\}|\\end\{(' + NUMBERED + r')\*?\}|(?<!\\)\\\[|\\\]', l):
        t = m.group(0)
        if t.startswith('\\begin') or t == '\\[':
            stack = (t, i)
        elif stack:
            envs.append((stack[0], stack[1], i))
            stack = None
for env, a, b in envs:
    body = '\n'.join(strip_comment(x) for x in src[a - 1:b])
    numbered_env = re.match(r'\\begin\{(' + NUMBERED + r')\}', env) is not None
    multi = re.match(r'\\begin\{(align|gather|flalign|alignat)\}', env) is not None
    # rows: split on \\ at top level of the environment (inner aligned/split blocks count as one row)
    rows = []
    if multi:
        depth, row_start, k = 0, 0, 0
        while k < len(body):
            if body.startswith('\\begin{', k):
                depth += 1
            elif body.startswith('\\end{', k):
                depth -= 1
            elif body.startswith('\\\\', k) and depth == 1:
                rows.append((row_start, k))
                row_start = k + 2
                k += 2
                continue
            k += 1
        rows.append((row_start, len(body)))
    else:
        rows = [(0, len(body))]
    for r0, r1 in rows:
        chunk = body[r0:r1]
        tag = re.search(r'\\tag\{([^}]*)\}', chunk)
        if tag:
            number = tag.group(1)
        elif numbered_env and not re.search(r'\\(nonumber|notag)\b', chunk) and chunk.strip(' \n') \
                and not re.fullmatch(r'\s*\\end\{\w+\*?\}\s*', chunk):
            eqno += 1
            number = str(eqno)
        else:
            continue
        core = re.sub(r'\\(begin|end)\{\w+\*?\}', lambda m: ' ' * len(m.group(0)), chunk)
        lead = len(core) - len(core.lstrip())
        la = a + body[:r0 + lead].count('\n')
        lb = a + body[:r0 + len(core.rstrip())].count('\n')
        if not multi:
            la, lb = a, b
        lab = re.search(r'\\label\{([^}]*)\}', chunk)
        name = f'Eq ({number})'
        items.append({'id': name, 'kind': 'equation', 'number': number, 'name': None,
                      'label': lab.group(1) if lab else None, 'section': section_of[la], 'lines': [[la, lb]]})
        text[name] = '\n'.join(src[la - 1:lb])

# ---- blueprint passages ------------------------------------------------------
stmt_by_lines = {tuple(map(tuple, x['lines'])): x for x in items if x['kind'] != 'equation'}
passage_is_statement = []
for p in json.load(open(PASSAGES, encoding='utf-8')):
    spans = [list(s) for s in p['spans']]
    file_stem = p['file'].replace('-locators.md', '').replace('.md', '')
    pname = f"{file_stem}: {p['heading']}"
    st = stmt_by_lines.get(tuple(map(tuple, spans)))
    if st:
        passage_is_statement.append([pname, st['id']])
        continue
    pid = f'Passage {pname}'
    items.append({'id': pid, 'kind': 'passage', 'number': None, 'name': pname, 'label': p['label'],
                  'section': section_of[spans[0][0]], 'lines': spans})
    text[pid] = '\n\n'.join('\n'.join(src[a - 1:b]) for a, b in spans)

# ---- enclosing item: the smallest other item whose lines contain this item's lines ----
def lineset(x):
    return set(n for a, b in x['lines'] for n in range(a, b + 1))


sets = {x['id']: lineset(x) for x in items}
for x in items:
    s = sets[x['id']]
    best = None
    for y in items:
        t = sets[y['id']]
        if y is x or not s < t:
            continue
        if best is None or len(t) < len(sets[best['id']]) or \
                (len(t) == len(sets[best['id']]) and y['kind'] != 'passage'):
            best = y
    x['enclosing'] = best['id'] if best else None

order = {'statement': 0, 'equation': 1, 'passage': 2}
items.sort(key=lambda x: (order['statement' if x['kind'] in KINDS else x['kind']], x['lines'][0][0], x['id']))
counts = {'statements': sum(1 for x in items if x['kind'] in KINDS),
          'displays': sum(1 for x in items if x['kind'] == 'equation'),
          'passages': sum(1 for x in items if x['kind'] == 'passage'),
          'passages that are statements': len(passage_is_statement)}
json.dump({'source': {'repository': 'https://github.com/elliotglazer/diophantine-z-q',
                      'commit': '97cec7fdd757d9a8e4f468151a47a6d3610fb2f2', 'file': 'diophantine_zq.tex',
                      'sha256': 'cb1148cd6c7769d2af3f1636b60ff0ada4b40431978d1e98d0c339274b3d792b'},
           'counts': counts, 'passages_that_are_statements': passage_is_statement,
           'items': [{k: x[k] for k in ('id', 'kind', 'number', 'name', 'label', 'section', 'enclosing', 'lines')}
                     for x in items]},
          open(OUT, 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
json.dump(text, open(TEXT, 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
print(json.dumps(counts))
