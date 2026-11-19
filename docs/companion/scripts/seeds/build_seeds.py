#!/usr/bin/env python3
"""Candidate declarations for every item and each repository: hints for the mapping, not judgements.

Deicyde/diophantine-z-q ("fork"):
  blueprint  - the blueprint pages (blueprint/roadmap/**.md, front matter `lean:`) whose locator
               section (blueprint/sources/*-locators.md) cites lines that meet the item's lines, as
               harvested at the pin by tools/harvest.py; each named declaration is checked against
               the fork's declaration index;
  lexical    - declarations whose name contains the words of a term the item defines (\\emph, \\textbf,
               \\textit, a statement's or passage's title).
nasqret/z-in-q-lean ("nasqret"):
  blueprint  - entries of docs/blueprint/sections/*.md (the README's twelve hypotheses are among them),
               ranked by tf-idf similarity of their text with the item's LaTeX;
  via_kernel - its declarations whose statement mentions a dependency-kernel declaration of the same
               name as one the fork's blueprint seeds for the item;
  lexical    - as for the fork.

Usage: python3 -I build_seeds.py <items.json> <items-text.json> <harvest-fork.json> <decls-fork.json>
       <decls-nasqret.json> <decls-ndep.json> <nasqret dir> <out json>
"""
import collections
import json
import math
import os
import re
import sys

(ITEMS, TEXT, HARVEST, DF, DN, DD, NAS, OUT) = sys.argv[1:9]
items = json.load(open(ITEMS, encoding='utf-8'))['items']
text = json.load(open(TEXT, encoding='utf-8'))
harvest = json.load(open(HARVEST, encoding='utf-8'))['records']
STOP = set('the and for with from that this its are any all one two set our over into each every some of on in to '
           'by at as an or be is it if a not let then there which where when such their than also only same both '
           'section proof lemma theorem proposition definition remark corollary passage statement opening'.split())


def load(path):
    rows = json.load(open(path, encoding='utf-8'))['declarations']
    return rows, {r['name']: r for r in rows if r['kind'] != 'example'}


fork_rows, fork = load(DF)
nas_rows, nas = load(DN)
dep_rows, dep = load(DD)


def split_name(name):
    last = name.split('.')[-1]
    parts = re.split(r'_+|(?<=[a-z0-9])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])', last)
    return [p.lower() for p in parts if p]


def stem(w):
    return w[:5]


def word_index(rows):
    idx = collections.defaultdict(set)
    for r in rows:
        if r['kind'] in ('example',) or r.get('private'):
            continue
        for w in split_name(r['name']):
            if len(w) >= 3:
                idx[stem(w)].add(r['name'])
    return idx


FORK_W, NAS_W = word_index(fork_rows), word_index(nas_rows)


def detex(s):
    s = re.sub(r'(?<!\\)%[^\n]*', ' ', s)
    s = re.sub(r'\\(label|ref|eqref|cite|begin|end)\*?(\[[^\]]*\])?\{[^}]*\}', ' ', s)
    s = re.sub(r'\\[a-zA-Z]+', ' ', s)
    return s


def words(s):
    return [w.lower() for w in re.findall(r'[A-Za-z]{3,}', s) if w.lower() not in STOP]


def terms_of(item):
    t = text.get(item['id'], '')
    terms = re.findall(r'\\(?:emph|textbf|textit)\{([^{}]*)\}', t)
    m = re.match(r'\\begin\{\w+\}\[([^\]]*)\]', t)
    if m:
        terms.append(m.group(1))
    if item['kind'] == 'passage':
        terms.append(item['name'].split(': ', 1)[1])
    out = []
    for x in terms:
        ws = [w for w in words(detex(x)) if not re.fullmatch(r'(appendix|section|statement|step|part)', w)]
        if ws and ws not in out:
            out.append(ws)
    return out


def lexical(item, widx, table, limit=12):
    found = {}
    for ws in terms_of(item):
        ws = list(dict.fromkeys(ws))[:4]
        need = len(ws) if len(ws) <= 2 else max(2, math.ceil(2 * len(ws) / 3))
        cnt = collections.Counter()
        for w in ws:
            for n in widx.get(stem(w), ()):
                cnt[n] += 1
        for n, c in cnt.items():
            if c >= need and n not in found:
                found[n] = (c / len(ws), ' '.join(ws))
    ranked = sorted(found.items(), key=lambda kv: (-kv[1][0], table[kv[0]]['vendored'],
                                                   table[kv[0]]['kind'] == 'field', len(kv[0])))
    return [{'name': n, 'kind': table[n]['kind'], 'standing': table[n]['standing'], 'file': table[n]['file'],
             'line': table[n]['line'], 'vendored': table[n]['vendored'], 'term': t, 'score': round(s, 2)}
            for n, (s, t) in ranked[:limit]], len(ranked)


def lines_of(x):
    return set(n for a, b in x['lines'] for n in range(a, b + 1))


# ---- fork: blueprint pages by line overlap -----------------------------------------
recs = []
for r in harvest:
    p = r['passage']
    rng = [tuple(x) for x in p['ranges']]
    if p['how'] == 'label':
        st = next((x for x in items if x['label'] == p['label'] and x['kind'] != 'passage'), None)
        rng = [tuple(st['lines'][0])] if st else []
    recs.append((r, set(n for a, b in rng for n in range(a, b + 1)),
                 f"{p['file'].replace('-locators.md', '').replace('.md', '')}: {p['heading']}"))


def fork_blueprint(item):
    s = lines_of(item)
    out = []
    for r, ls, pname in recs:
        if not ls & s:
            continue
        rel = 'same lines' if ls == s else 'page cites more' if s < ls else 'page cites part' if ls < s else 'overlap'
        decls = []
        for d in r['decls']:
            nm = d['name']
            row = fork.get(nm) or (fork.get(d['resolved'].split(':', 1)[1]) if (d['resolved'] or '').startswith('suffix:') else None)
            decls.append({'name': row['name'] if row else nm, 'in_index': bool(row),
                          'standing': row['standing'] if row else None,
                          'file': row['file'] if row else None, 'line': row['line'] if row else None})
        out.append({'page': r['page'], 'title': r['title'], 'passage': pname, 'lines': rel,
                    'statement': r['statement'], 'proof': r['proof'], 'declarations': decls})
    order = {'same lines': 0, 'page cites part': 1, 'page cites more': 2, 'overlap': 3}
    out.sort(key=lambda x: (order[x['lines']], x['page']))
    return out


# ---- nasqret: blueprint entries ---------------------------------------------------
entries = []
secdir = os.path.join(NAS, 'docs', 'blueprint', 'sections')
for f in sorted(os.listdir(secdir)):
    if not f.endswith('.md'):
        continue
    t = open(os.path.join(secdir, f), encoding='utf-8').read()
    for m in re.finditer(r'^### (\w+) (\d+)\. (.+?)\n(.*?)(?=^<a id=|^### |\Z)', t, flags=re.M | re.S):
        kind, num, title, body = m.groups()
        link = re.search(r'\[Lean (?:statement|definition|proof)\]\(https://github\.com/([^/]+/[^/]+)/blob/(\w+)/([^#)]+)#L(\d+)-L(\d+)\)', body)
        decl, repo = None, None
        if link:
            repo = link.group(1)
            table = nas_rows if repo == 'nasqret/z-in-q-lean' else dep_rows
            a, b = int(link.group(4)), int(link.group(5))
            hits = [r for r in table if r['file'] == link.group(3) and a <= r['line'] <= b and r['kind'] != 'field']
            decl = hits[0]['name'] if hits else None
        statement = body.split('**')[0]
        entries.append({'number': int(num), 'kind': kind, 'title': title.strip(), 'file': f,
                        'text': title + ' ' + statement, 'lean_repo': repo, 'declaration': decl})
readme = open(os.path.join(NAS, 'README.md'), encoding='utf-8').read()
readme_hyps = {int(n): t for n, t in re.findall(r'^\*\*(\d+)\. ([^*]+)\*\*', readme, flags=re.M)}


def toks(s):
    s = re.sub(r'\\[a-zA-Z]+', ' ', s)
    return [w.lower() for w in re.findall(r'[A-Za-z]{3,}|\d+', s) if w.lower() not in STOP]


docs = [collections.Counter(toks(e['text'])) for e in entries]
df = collections.Counter(w for d in docs for w in d)
N = len(docs)


def vec(c):
    v = {w: (1 + math.log(n)) * math.log((N + 1) / (df.get(w, 0) + 1)) for w, n in c.items() if w in df}
    norm = math.sqrt(sum(x * x for x in v.values())) or 1
    return {w: x / norm for w, x in v.items()}


evecs = [vec(d) for d in docs]


def nas_blueprint(item, limit=5, floor=0.12):
    v = vec(collections.Counter(toks(text.get(item['id'], ''))))
    sc = [(sum(v.get(w, 0) * x for w, x in ev.items()), k) for k, ev in enumerate(evecs)]
    sc.sort(reverse=True)
    out = []
    for s, k in sc[:limit]:
        if s < floor:
            break
        e = entries[k]
        row = (nas if e['lean_repo'] == 'nasqret/z-in-q-lean' else dep).get(e['declaration'] or '')
        out.append({'entry': e['number'], 'kind': e['kind'], 'title': e['title'], 'section_file': e['file'],
                    'readme_hypothesis': e['number'] in readme_hyps, 'score': round(s, 3),
                    'declaration': e['declaration'],
                    'declaration_repository': e['lean_repo'],
                    'standing': row['standing'] if row else None})
    return out


# ---- nasqret: declarations that mention a kernel declaration seeded for the item ----
ID = re.compile(r"[A-Za-z_][\w'!?]*(?:\.[A-Za-z_][\w'!?]*)*")
mentions = collections.defaultdict(set)
dep_last = collections.Counter(n.split('.')[-1] for n in dep)
for r in nas_rows:
    for tok in set(ID.findall(r['snippet'])):
        mentions[tok].add(r['name'])
        mentions[tok.split('.')[-1]].add(r['name'])


def via_kernel(fork_bp, limit=15):
    out = {}
    for page in fork_bp:
        for d in page['declarations']:
            nm = d['name']
            if nm not in dep:
                continue
            last = nm.split('.')[-1]
            users = set(mentions.get(nm, ()))
            if len(last) >= 6 and dep_last[last] == 1:
                users |= mentions.get(last, set())
            for u in users:
                if u != nm:
                    out.setdefault(u, set()).add(nm)
    ranked = sorted(out.items(), key=lambda kv: (-len(kv[1]), len(kv[0])))
    return [{'name': u, 'standing': nas[u]['standing'], 'file': nas[u]['file'], 'line': nas[u]['line'],
             'mentions': sorted(ks)} for u, ks in ranked[:limit] if u in nas], len(ranked)


seeds = {}
stats = collections.Counter()
for it in items:
    fb = fork_blueprint(it)
    fl, fl_n = lexical(it, FORK_W, fork)
    nl, nl_n = lexical(it, NAS_W, nas)
    vk, vk_n = via_kernel(fb)
    nb = nas_blueprint(it)
    seeds[it['id']] = {
        'terms': [' '.join(t) for t in terms_of(it)],
        'fork': {'blueprint': fb, 'lexical': fl, 'lexical_total': fl_n},
        'nasqret': {'blueprint': nb, 'via_kernel': vk, 'via_kernel_total': vk_n, 'lexical': nl, 'lexical_total': nl_n},
    }
    stats['items'] += 1
    stats['items with a fork blueprint page'] += bool(fb)
    stats['items with a fork lexical match'] += bool(fl)
    stats['items with a nasqret blueprint entry'] += bool(nb)
    stats['items with a nasqret via-kernel match'] += bool(vk)
    stats['items with a nasqret lexical match'] += bool(nl)
    stats['fork blueprint declarations not in the index'] += sum(1 for p in fb for d in p['declarations'] if not d['in_index'])
json.dump({'note': 'Hints for the mapping session. Nothing here is a judged relation.',
           'stats': stats, 'nasqret_blueprint_entries': len(entries),
           'nasqret_readme_hypotheses': sorted(readme_hyps), 'items': seeds},
          open(OUT, 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
print(json.dumps(stats, indent=0))
