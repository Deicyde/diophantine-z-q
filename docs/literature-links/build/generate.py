#!/usr/bin/env python3
"""Write Literature Links annotations and an index from the two harvests.

Usage: generate.py <items.json> <out-dir> <name>=<harvest.json>=<repo-url>=<commit> ...
"""
import collections
import json
import os
import re
import sys

ITEMS = json.load(open(sys.argv[1], encoding='utf-8'))
OUT = sys.argv[2]
REPOS = []
for arg in sys.argv[3:]:
    name, path, url, commit = arg.split('=')
    REPOS.append({'name': name, 'h': json.load(open(path, encoding='utf-8')), 'url': url, 'commit': commit})

EXT = 'io.github.deicyde.z-in-q-companion'
MS_COMMIT = '97cec7fdd757d9a8e4f468151a47a6d3610fb2f2'
MS_SHA = 'cb1148cd6c7769d2af3f1636b60ff0ada4b40431978d1e98d0c339274b3d792b'
MS_URL = f'https://raw.githubusercontent.com/elliotglazer/diophantine-z-q/{MS_COMMIT}/diophantine_zq.tex'
MS_BLOB = f'https://github.com/elliotglazer/diophantine-z-q/blob/{MS_COMMIT}/diophantine_zq.tex'
KIND = {'theorem': 'theorem', 'lemma': 'lemma', 'proposition': 'proposition', 'corollary': 'theorem',
        'definition': 'definition', 'remark': 'remark'}
BY_LABEL = {x['label']: x for x in ITEMS}


def slug(s):
    return re.sub(r'-+', '-', re.sub(r'[^a-z0-9]+', '-', s.replace('$', '').lower())).strip('-')


def passage_id(p):
    return p['file'].replace('-locators.md', '').replace('.md', '') + '/' + slug(p['heading'])


def passage_kind(p):
    if p['label']:
        return KIND[BY_LABEL[p['label']]['kind']]
    m = re.match(r'(Theorem|Lemma|Proposition|Corollary|Definition|Remark) [0-9A-H]+\.[0-9]+$', p['heading'])
    if m:
        return KIND[m.group(1).lower()]
    if p['heading'].startswith('Proof of') or p['heading'].endswith(' proof'):
        return 'proof'
    return None


def subject_ends(p):
    title = p['heading'].replace('$', '')
    if p['label']:
        return [{'location': {'label': p['label']}, 'title': title}]
    return [{'location': {'lines': [a, b]}, 'title': title} for a, b in p['ranges']]


def spans(p):
    if p['label']:
        it = BY_LABEL[p['label']]
        return [(it['start'], it['end'])]
    return [tuple(r) for r in p['ranges']]


def write_json(path, obj):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(obj, f, indent=2, ensure_ascii=False)
        f.write('\n')


os.makedirs(OUT, exist_ok=True)
ann_root = os.path.join(OUT, 'annotations')
write_json(os.path.join(ann_root, '_defaults.json'), {
    'subject': {
        'type': 'latex', 'uri': MS_URL, 'version': MS_COMMIT, 'sha256': MS_SHA,
        'citation': {'id': 'z_in_q_2026', 'type': 'manuscript', 'title': 'ℤ is Diophantine in ℚ',
                     'issued': {'date-parts': [[2026, 11, 5]]},
                     'URL': 'https://github.com/elliotglazer/diophantine-z-q',
                     'note': 'Manuscript dated November 5, 2026. Author field intentionally omitted, as in the repository\'s CITATION.bib.'},
    }
})

passages = {}          # id -> passage
links = collections.defaultdict(lambda: collections.defaultdict(list))   # id -> repo -> [(decl, page)]
counts = {}
for repo in REPOS:
    write_json(os.path.join(ann_root, repo['name'], '_defaults.json'),
               {'object': {'type': 'lean', 'uri': repo['url'], 'version': repo['commit']}})
    by_chapter = collections.defaultdict(list)
    n_ann = n_decl = n_empty = 0
    for r in sorted(repo['h']['records'], key=lambda r: (r['chapter'], r['page'], r['passage']['file'], r['passage']['anchor'])):
        p = r['passage']
        pid = passage_id(p)
        passages[pid] = p
        ann = {'id': pid, 'subject': subject_ends(p)}
        obj = []
        decl_lines = {}
        for d in r['decls']:
            loc = {'declaration': d['name']}
            if d['module']:
                loc['module'] = d['module']
            obj.append({'location': loc, 'extensions': {EXT: {'path': d['path'], 'line': d['line']}}})
            decl_lines[d['name']] = f"{d['path']}#L{d['line']}"
            links[pid][repo['name']].append((d, r['page']))
            n_decl += 1
        ann['object'] = obj
        if not obj:
            n_empty += 1
        k = passage_kind(p)
        if k:
            ann['kind'] = k
        what = {'cited': 'takes its statement from this passage', 'bridged': 'bridges this passage to the Lean',
                'background': 'is background for this passage'}.get(r['origin'], 'cites this passage')
        ann['note'] = (f"Blueprint page \"{r['title']}\" {what} (origin: {r['origin']}). "
                       + ("The page names no Lean declaration. " if not obj else "")
                       + "Harvested from the repository's blueprint; the relation was not assessed.")
        ann['extensions'] = {EXT: {
            'page': r['page'], 'article_id': r['article_id'], 'origin': r['origin'],
            'statement': r['statement'], 'proof': r['proof'],
            'locator': f"blueprint/sources/{p['file']}#{p['anchor']}", 'span_read_from': p['how']}}
        ann['extensions'][EXT] = {k: v for k, v in ann['extensions'][EXT].items() if v is not None}
        by_chapter[r['chapter']].append(ann)
        n_ann += 1
    for ch, anns in by_chapter.items():
        path = os.path.join(ann_root, repo['name'], ch + '.jsonl')
        with open(path, 'w', encoding='utf-8') as f:
            for a in anns:
                f.write(json.dumps(a, ensure_ascii=False) + '\n')
    counts[repo['name']] = {'annotations': n_ann, 'declaration ends': n_decl, 'without declaration': n_empty,
                            'chapters': {ch: len(a) for ch, a in sorted(by_chapter.items())}}


def overlaps(a, b):
    return a[0] <= b[1] and b[0] <= a[1]


# Numbered items: which passages touch their statement lines, per repository.
item_rows = []
unlinked = []
for it in ITEMS:
    st = (it['start'], it['end'])
    per = {}
    for repo in REPOS:
        names = []
        for pid, p in passages.items():
            if any(overlaps(st, s) for s in spans(p)):
                for d, _ in links[pid].get(repo['name'], []):
                    if d['name'] not in [x['name'] for x in names]:
                        names.append(d)
        per[repo['name']] = names
    item_rows.append((it, per))
    if not any(per.values()):
        unlinked.append(it)
with open(os.path.join(ann_root, 'unlinked.jsonl'), 'w', encoding='utf-8') as f:
    for it in unlinked:
        f.write(json.dumps({
            'id': 'item/' + it['label'],
            'subject': [{'location': {'label': it['label']},
                         'title': it['name'] + (f" ({it['title']})" if it['title'] else '')}],
            'object': [], 'kind': KIND[it['kind']],
            'note': 'No blueprint page in either repository cites this statement\'s lines. Unlinked, not a checked absence.',
        }, ensure_ascii=False) + '\n')


def blob(repo, d):
    return f"{repo['url']}/blob/{repo['commit']}/{d['path']}#L{d['line']}"


def ms_link(a, b):
    return f"[{a}–{b}]({MS_BLOB}#L{a}-L{b})" if a != b else f"[{a}]({MS_BLOB}#L{a})"


def cell(repo, decls, limit=3):
    if not decls:
        return '—'
    shown = ', '.join(f"[`{d['name'].split('.')[-1]}`]({blob(repo, d)})" for d in decls[:limit])
    more = f" +{len(decls) - limit}" if len(decls) > limit else ''
    return f"{len(decls)}: {shown}{more}"


L = []
L.append('# Index: the 5 November manuscript against two repositories\n')
L.append('Generated by `build/generate.py`. Every link here is harvested from a repository\'s own blueprint; none was checked for faithfulness.\n')
L.append('## Numbered statements\n')
L.append('A declaration is listed against a statement when a blueprint page that names it cites lines overlapping the statement\'s own lines. Proof lines are not counted here; they appear under Passages.\n')
hdr = '| Statement | Title | Lines | ' + ' | '.join(r['name'] for r in REPOS) + ' |'
L.append(hdr)
L.append('|---|---|---|' + '---|' * len(REPOS))
for it, per in item_rows:
    title = (it['title'] or '').replace('|', '\\|')
    L.append(f"| {it['name']} | {title} | {ms_link(it['start'], it['end'])} | "
             + ' | '.join(cell(r, per[r['name']]) for r in REPOS) + ' |')
L.append('\n## Passages\n')
L.append('One row per manuscript passage that a blueprint page cites, in manuscript order.\n')
L.append('| Passage | Lines | ' + ' | '.join(r['name'] for r in REPOS) + ' | Same declarations? |')
L.append('|---|---|' + '---|' * len(REPOS) + '---|')
same = differ = 0
only = collections.Counter()
for pid, p in sorted(passages.items(), key=lambda kv: (spans(kv[1])[0], kv[0])):
    per = {}
    for repo in REPOS:
        seen = []
        for d, _ in links[pid].get(repo['name'], []):
            if d['name'] not in [x['name'] for x in seen]:
                seen.append(d)
        per[repo['name']] = seen
    sets = [frozenset(d['name'] for d in per[r['name']]) for r in REPOS]
    if len(set(sets)) == 1:
        verdict = 'yes'
        same += 1
    else:
        differ += 1
        parts = []
        for r, s in zip(REPOS, sets):
            extra = s - frozenset().union(*[t for t in sets if t is not s])
            if extra:
                parts.append(f"{len(extra)} only in {r['name']}")
                only[r['name']] += len(extra)
        verdict = '; '.join(parts) or 'differ'
    lines = ', '.join(ms_link(a, b) for a, b in spans(p))
    L.append(f"| `{pid}` | {lines} | " + ' | '.join(cell(r, per[r['name']]) for r in REPOS) + f" | {verdict} |")
open(os.path.join(OUT, 'INDEX.md'), 'w', encoding='utf-8').write('\n'.join(L) + '\n')

summary = {
    'manuscript': {'url': MS_URL, 'commit': MS_COMMIT, 'sha256': MS_SHA, 'numbered statements': len(ITEMS)},
    'repositories': {r['name']: {'url': r['url'], 'commit': r['commit'], **counts[r['name']],
                                 'blueprint pages': r['h']['stats']['pages'],
                                 'pages with no manuscript passage': r['h']['stats'].get('pages with no manuscript passage', 0)}
                     for r in REPOS},
    'passages': len(passages), 'passages with the same declarations in every repository': same,
    'passages that differ': differ, 'declarations only in one repository': dict(only),
    'numbered statements with a link in some repository': len(ITEMS) - len(unlinked),
    'numbered statements unlinked': len(unlinked),
    'unlinked': [it['name'] for it in unlinked],
    'linked statements': {it['name']: {r: len(v) for r, v in per.items()} for it, per in item_rows if any(per.values())},
}
write_json(os.path.join(OUT, 'summary.json'), summary)
print(json.dumps({k: v for k, v in summary.items() if k not in ('unlinked', 'linked statements')}, indent=1, ensure_ascii=False))
print('linked statements:', summary['linked statements'])
