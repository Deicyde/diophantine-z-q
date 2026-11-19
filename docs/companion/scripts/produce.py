"""Write manuscript/annotations/: the Literature Links annotations of the overlay of [M]'s PDF.

Adapted from the Yang–Mills companion's producer (ym-companion, scripts/produce.py), standard
library only. formal-companion's route B: this producer writes the files and `cf overlay sync`
records them; formal-companion docs/overlay.md section 7 is the layout.

Reads data/items.json (the items of [M] at its pin), data/regions.json (their regions on
diophantine_zq.pdf), data/mapping.json (one verdict per item and repository), data/notes-short.json
(two-sentence forms of the longer notes) and data/linked-decls.json (the linked declarations of
[F], [N] and [N]'s dependency at their pins), and writes

  manuscript/annotations/_defaults.json             the PDF
  manuscript/annotations/<section>/<item>/<name>.json

Per item and repository: one record for the key declarations together, carrying the relation of
the verdict's status (for `parts`, one `hasPart` record per key declaration); for an [N] verdict
carried by its dependency, the same with the dependency's declarations, role `support`; one
`relatedMatch` record per other linked declaration; a checked absence (`noMatch`, object the
repository at its pin) for `no-match` and `not-formalized-not-needed`. Every Lean end is written
whole, names its repository and pin, and carries `<name>@<repository>` as its declaration id and
`<kind> · <repository>` as its declaration kind, so that the viewer keeps the repositories apart.
A dependency end carries no snippet: that repository states no licence.

With `--index fork=<decls.json> --index ndep=<decls.json>` (the indexes scripts/lean/build.sh
writes; [N]'s is data/decls-nasqret.json), it first rewrites data/linked-decls.json, checking each
index against its data/decls-*.json.sha256 and every linked declaration against its index.

Usage: python3 -I scripts/produce.py [--index fork=<path>] [--index ndep=<path>] [<repository root>]
"""
import collections
import hashlib
import json
import os
import re
import shutil
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'mapping'))
from standing import REDUCES, carrying as carrying_links, link_standing, open_assumes  # noqa: E402

NS = 'org.mathlib-initiative.formal-companion.overlay'
ROLES = ('key', 'attributed', 'support', 'example', 'helper')
UNSAFE = re.compile(r'[^A-Za-z0-9._-]')
RESERVED = re.compile(r'(?i)(con|prn|aux|nul|com[0-9]|lpt[0-9])')
MAX_NAME = 120
SOURCE_ID = 'z-in-q-2026-11-05'
PDF_URL = 'https://raw.githubusercontent.com/elliotglazer/diophantine-z-q/{pin}/diophantine_zq.pdf'
SRC_REPO = 'https://github.com/elliotglazer/diophantine-z-q'
REPOS = ('fork', 'nasqret')
# The name a Lean end carries on screen, per repository of a link (`repo` in data/mapping.json).
TAG = {'fork': 'fork', 'nasqret': 'nasqret', 'ndep': 'nasqret-dependency'}
KIND_TAG = {'fork': 'fork', 'nasqret': 'nasqret', 'ndep': 'nasqret dependency'}
LABEL = {'fork': '[F] Deicyde/diophantine-z-q', 'nasqret': '[N] nasqret/z-in-q-lean'}

# The verdict's status (docs/taxonomy.md) -> the relation of its key link (the table of out/REPORT-2.md).
RELATION = {
    'exact': 'exactMatch', 'definition-match': 'exactMatch',
    'close': 'closeMatch', 'definition-close': 'closeMatch',
    'stronger': 'broadMatch',
    'weaker': 'narrowMatch', 'missing-hypothesis': 'narrowMatch',
    'parts': 'hasPart',
    'inlined': 'relatedMatch', 'differs': 'relatedMatch', 'definition-differs': 'relatedMatch',
    'no-match': 'noMatch', 'not-formalized-not-needed': 'noMatch',
    'unclear': None,
}
# The status of the record: `formalized` only where the repository states the item and proves it
# (or, for a definition, defines it); an assumed or conditional statement is `partial`.
FORMALIZED = {'exact', 'definition-match', 'close', 'definition-close', 'stronger'}
ABSENT = {'no-match', 'not-formalized-not-needed'}
FINDINGS = {'stronger', 'weaker', 'missing-hypothesis', 'differs', 'definition-differs'}
FINDING_SUMMARY = {
    'stronger': 'states more than [M] prints',
    'weaker': 'proves less than [M] prints',
    'missing-hypothesis': 'needs a hypothesis [M] does not print',
    'differs': 'states a different claim; neither implies the other',
    'definition-differs': 'defines a different object',
}
KIND_TITLE = {'definition': 'Definition', 'lemma': 'Lemma', 'theorem': 'Theorem', 'proposition': 'Proposition',
              'corollary': 'Corollary', 'remark': 'Remark'}
ABBREVIATION = re.compile(r'(?:\b(?:e\.g|i\.e|a\.e|cf|Prop|Thm|Lem|Cor|Sec|Eq|Eqs|pp?|resp|vs|approx|al|Fig|No)\.|'
                          r'\b[A-Z]\.)$')


def sentences(text):
    out, cur = [], ''
    for part in re.split(r'(?<=[.!?])\s+', ' '.join((text or '').split())):
        cur = f'{cur} {part}'.strip()
        if not ABBREVIATION.search(cur):
            out.append(cur)
            cur = ''
    return out + ([cur] if cur else [])


def file_name(key, suffix='', force_hash=False):
    """formal-companion's rule (scripts/overlay/shards.py): unsafe characters as `-`, and a name that is
    too long, reserved, `_defaults.json` or equal to another ignoring case ends in a hash of the key."""
    stem = UNSAFE.sub('-', key)
    if stem.startswith('.'):
        stem = '-' + stem[1:]
    if force_hash or len(stem) + len(suffix) > MAX_NAME or RESERVED.fullmatch(stem.split('.', 1)[0]) \
            or (stem + suffix).lower() == '_defaults.json':
        tail = '-' + hashlib.sha256(key.encode('utf-8')).hexdigest()[:10]
        stem = stem[:MAX_NAME - len(suffix) - len(tail)] + tail
    return stem + suffix


def title_of(item):
    if item['kind'] == 'equation':
        return f"Eq. ({item['number']})"
    if item['kind'] == 'passage':
        stem, _, heading = item['name'].partition(': ')
        return f'Passage ({stem}): {heading}'
    return f"{KIND_TITLE[item['kind']]} {item['number']}"


def and_list(names):
    return ' and '.join(names) if len(names) < 3 else ', '.join(names[:-1]) + ' and ' + names[-1]


def short_names(pairs):
    """The open hypotheses of (link repository, Prop) pairs; a Prop the repository proves only from others
    names them."""
    pairs = list(dict.fromkeys(pairs))
    if len(pairs) > 3:
        return f'{len(pairs)} named hypotheses'
    out = []
    for lrepo, a in pairs:
        via = REDUCES[lrepo].get(a)
        out.append(f"{a} (itself proved only from {and_list(list(via))})" if via else a)
    return and_list(out)


def open_pairs(links, repo):
    return [(l.get('repo', repo), a) for l in links for a in open_assumes(l, repo)]


def link_phrase(l, repo):
    """The standing of one linked declaration, for a record that carries only it."""
    s = link_standing(l, repo)
    return {'proved': 'proved', 'assumed': 'assumed, not proved', 'definition': 'a definition',
            'sorry': 'proof has sorry'}.get(s) or 'proved only from ' + short_names(open_pairs([l], repo))


def standing_phrase(v, carrying, repo):
    s = v['standing']
    if s == 'proved':
        return 'proved'
    if s == 'conditional':
        cond = [l for l in carrying if link_standing(l, repo) == 'conditional']
        if v['status'] == 'parts' or v.get('via_dependency'):
            return 'proved only from ' + short_names(open_pairs(cond, repo))
        # Each key states the whole item: the one with the fewest open hypotheses speaks for it.
        best = min(cond, key=lambda l: len(open_assumes(l, repo)))
        more = ', or by another key from other hypotheses' if len(cond) > 1 else ''
        return 'proved only from ' + short_names(open_pairs([best], repo)) + more
    if s == 'assumed':
        if v['status'] == 'parts' or v.get('via_dependency'):
            parts = [l['decl'] for l in carrying if link_standing(l, repo) == 'assumed']
            return f'in part assumed, not proved ({and_list(parts)})'
        return 'assumed, not proved'
    if s == 'definition':
        return 'a definition' if v['status'].startswith('definition-') else 'stated, neither proved nor assumed'
    if s == 'sorry':
        return 'stated, proof has sorry'
    return 'nothing to formalize' if v['status'] == 'not-formalized-not-needed' else 'no counterpart'


def provenance(v, repo):
    ve = v['verification']
    steps = ve['steps']
    method = 'mapper and verifier agents, ' + ('agreed' if ve['mapper_verifier_agree'] else 'a judge ruled')
    if ve.get('finding') == 'confirmed':
        method += '; finding confirmed by two skeptics' + (', then by two more after a judge revised it'
                                                           if ve.get('second_round') else '')
    elif ve.get('finding') == 'withdrawn':
        method += '; claimed finding withdrawn after a skeptic refuted it'
    elif 'post-skeptic judge' in steps:
        method += '; a judge ruled after a skeptic refuted the claim'
    if ve.get('absence') == 'confirmed':
        method += '; absence confirmed by a skeptic'
    if ve.get('correction'):
        method += '; note corrected after a review of the headline statements'
    if ve.get('review_status'):
        method += f"; status changed from {ve['review_status']['from']} after an independent review"
    elif ve.get('review'):
        method += '; note corrected after an independent review'
    which = 'and its dependency at their pins' if repo == 'nasqret' else 'at its pin'
    method += f"; source of {LABEL[repo].split(' ', 1)[1]} {which} read, not built"
    return {'actor': 'agent', 'method': method, 'confirmed_by_human': False}


def note_of(item_id, repo, v, carrying, short, own=None, read=()):
    """The record's note. `own` is the one link a `hasPart` or `relatedMatch` record carries, when its
    standing is not the verdict's; `read` are the dependency's declarations an [N] verdict that has
    declarations of its own reads through, which the note names instead of linking."""
    body = short.get(f'{item_id}|{repo}')
    if body is None:
        s = sentences(v['note'])
        if len(s) > 2:
            sys.exit(f'{item_id}|{repo}: note of {len(s)} sentences has no short form in data/notes-short.json')
        body = ' '.join(s)
    head = f'{LABEL[repo]}, {standing_phrase(v, carrying, repo)}'
    if v.get('via_dependency'):
        head += ', through its dependency'
    if own is not None and link_phrase(own, repo) != standing_phrase(v, carrying, repo):
        head += f"; {own['decl']} {link_phrase(own, repo)}"
    if read:
        head += f"; through its dependency's {and_list(list(read))}"
    if v['verification'].get('finding') == 'confirmed':
        head += f"; confirmed finding ({v['status']})"
    return f'{head}: {body}'


def linked_decls(root, indexes):
    """Rewrite data/linked-decls.json: each declaration data/mapping.json names, from the full indexes."""
    paths = {'nasqret': os.path.join(root, 'data', 'decls-nasqret.json'), **indexes}
    if set(paths) != {'fork', 'nasqret', 'ndep'}:
        sys.exit('give --index fork=<path> and --index ndep=<path>')
    rows = {}
    pins = {}
    for repo, path in paths.items():
        if repo != 'nasqret':
            want = open(os.path.join(root, 'data', f'decls-{repo}.json.sha256')).read().split()[0]
            h = hashlib.sha256()
            with open(path, 'rb') as f:
                for block in iter(lambda: f.read(1 << 20), b''):
                    h.update(block)
            if h.hexdigest() != want:
                sys.exit(f'{path} is not the index data/decls-{repo}.json.sha256 names')
        index = json.load(open(path, encoding='utf-8'))
        pins[repo] = {'repository': index['repository'], 'commit': index['commit']}
        rows[repo] = collections.defaultdict(list)
        for r in index['declarations']:
            rows[repo][r['name']].append(r)
    mapping = json.load(open(os.path.join(root, 'data', 'mapping.json'), encoding='utf-8'))
    out = {k: {} for k in paths}
    for rec in mapping['items']:
        for repo in REPOS:
            for l in rec[repo]['lean']:
                lrepo = l.get('repo', repo)
                cands = rows[lrepo].get(l['decl'])
                if not cands:
                    sys.exit(f"{rec['id']}|{repo}: {l['decl']} is not in the {lrepo} index")
                path = l['where'].split(':')[0]
                same = [r for r in cands if r['file'] == path]
                if not same:
                    sys.exit(f"{rec['id']}|{repo}: {l['decl']} is not declared in {lrepo} {path}")
                r = same[0]
                if r['standing'] != l['standing']:
                    sys.exit(f"{rec['id']}|{repo}: {l['decl']} has standing {r['standing']} in the index")
                # The dependency states no licence: its declarations are named, never quoted.
                fields = ('kind', 'module', 'file', 'line', 'private', 'standing') + (() if lrepo == 'ndep' else ('snippet',))
                out[lrepo].setdefault(l['decl'], {})[r['file']] = {k: r.get(k) for k in fields}
    doc = {'about': 'The declarations data/mapping.json links, per repository, from the declaration indexes '
                    '(scripts/lean/build.sh; data/decls-nasqret.json and the sha256 of the other two in '
                    'data/decls-*.json.sha256); keyed by repository, name, then file.',
           'pins': pins, 'decls': {k: dict(sorted(v.items())) for k, v in out.items()}}
    with open(os.path.join(root, 'data', 'linked-decls.json'), 'w', encoding='utf-8') as f:
        json.dump(doc, f, indent=1, ensure_ascii=False, sort_keys=True)
        f.write('\n')


def main():
    args = sys.argv[1:]
    indexes = {}
    while args[:1] == ['--index']:
        repo, _, path = args[1].partition('=')
        indexes[repo], args = path, args[2:]
    root = args[0] if args else os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    if indexes:
        linked_decls(root, indexes)
    data = lambda n: json.load(open(os.path.join(root, 'data', n), encoding='utf-8'))
    items = {it['id']: it for it in data('items.json')['items']}
    regions, mapping, decls = data('regions.json'), data('mapping.json'), data('linked-decls.json')
    short = data('notes-short.json')['notes']
    pins = mapping['pins']
    lean = {'fork': pins['fork'], 'nasqret': pins['nasqret'], 'ndep': pins['nasqret']['dependency']}
    for repo, p in lean.items():
        if decls['pins'][repo] != {'repository': p['repository'], 'commit': p['commit']}:
            sys.exit(f'linked-decls.json is of another {repo} revision')
    pin = pins['manuscript']['commit']
    pdf = regions['pdf']
    if pdf['url'] != PDF_URL.format(pin=pin):
        sys.exit('regions.json is of another PDF')

    defaults = {
        'subject': {
            'type': 'pdf', 'uri': pdf['url'], 'sha256': pdf['sha256'],
            'citation': {'id': SOURCE_ID, 'type': 'manuscript', 'title': 'ℤ is Diophantine in ℚ',
                         'author': [], 'issued': {'date-parts': [[2026, 11, 5]]},
                         'version': f'manuscript dated November 5, 2026, commit {pin}',
                         'URL': f'{SRC_REPO}/tree/{pin}'},
            'extensions': {NS: {'source_id': SOURCE_ID, 'bytes': pdf['bytes'], 'physical_page_count': pdf['pages']}}},
    }

    def lean_end(l, role, repo, finding=None):
        """A Lean end, written whole: an end with its own `uri` takes nothing from a template."""
        lrepo = l.get('repo', repo)
        p = lean[lrepo]
        d = decls['decls'][lrepo][l['decl']][l['where'].split(':')[0]]
        kind = f"{d['kind']} · {KIND_TAG[lrepo]}"
        if d['standing'] == 'proved' and open_assumes(l, repo):
            kind += ' · conditional'
        elif d['standing'] in ('assumed', 'sorry'):
            kind += f" · {d['standing']}"
        ext = {'declaration': {'id': f"{l['decl']}@{TAG[lrepo]}", 'kind': kind}}
        if d.get('snippet'):
            ext['snippet'] = {'text': d['snippet'], 'line': d['line'], 'truncated': d['snippet'].endswith('…')}
        ext['destination'] = {'resolution': 'exact', 'href': f"{p['repository']}/blob/{p['commit']}/{d['file']}",
                              'fragment': f"L{d['line']}"}
        if d.get('private'):
            ext['declaration']['private'] = True
        if d['standing'] == 'sorry':
            ext['declaration']['sorry'] = 'proof'
        if finding:
            ext['declaration_verdict'] = finding
        return {'type': 'lean', 'uri': p['repository'], 'version': p['commit'],
                'location': {'declaration': l['decl'], 'module': d['module']}, 'role': role, 'extensions': {NS: ext}}

    out_dir = os.path.join(root, 'manuscript', 'annotations')
    if os.path.isdir(out_dir):
        shutil.rmtree(out_dir)
    os.makedirs(out_dir)
    counts = collections.Counter()
    files = {}
    for rec in mapping['items']:
        it = items[rec['id']]
        regs = regions['items'][rec['id']]
        subject = [{'location': {'page': r['page'], 'rect': r['rect']}, 'title': title_of(it),
                    'extensions': {NS: {'region': f"{it['id']}#{n}" if len(regs) > 1 else it['id']}}}
                   for n, r in enumerate(regs)]
        pages = sorted({r['page'] for r in regs})
        # The item's verdicts: each repository's confirmed finding, on every record of the item, since
        # the viewer reads an item's verdicts from its first record.
        verdicts = []
        for repo in REPOS:
            v = rec[repo]
            if v['verification'].get('finding') == 'confirmed':
                verdicts.append({
                    'verdict': 'deviation', 'status': 'unconfirmed',
                    'summary': f"{LABEL[repo]} {FINDING_SUMMARY[v['status']]} ({v['status']}).",
                    'evidence': [s['reason'] for s in v['verification'].get('skeptics', []) if not s.get('refuted')],
                    'provenance': {'actor': 'agent', 'method': 'two skeptics, each reading the LaTeX of [M] and the '
                                   'source of the repository, failed to refute it', 'confirmed_by_human': False}})
        records = []  # (file key, record)
        for repo in REPOS:
            v = rec[repo]
            if not v['judged']:
                records.append((f'unjudged@{repo}', {'id': it['id'], 'kind': it['kind'], 'note': 'Not yet judged.',
                                                     'subject': subject, 'object': [],
                                                     'extensions': {NS: {'locator': {'physical': pages}}}}))
                counts[f'{repo}.not_yet_judged'] += 1
                continue
            seen = {}
            for l in v['lean']:  # a declaration linked twice keeps its first, key-most link
                k = (l.get('repo', repo), l['decl'])
                if k not in seen or (l['role'] == 'key' and seen[k]['role'] != 'key'):
                    seen[k] = l
            links = list(seen.values())
            # Where [N] has declarations of its own, the dependency's are named in the note, not linked.
            read = [] if v.get('via_dependency') else [l['decl'] for l in links if l.get('repo') == 'ndep']
            links = [l for l in links if v.get('via_dependency') or l.get('repo') != 'ndep']
            carrying = carrying_links(dict(v, lean=links))
            rest = [l for l in links if l not in carrying]
            relation = RELATION[v['status']]
            confirmed = v['verification'].get('finding') == 'confirmed'
            status = 'not_formalized' if v['status'] in ABSENT else \
                'formalized' if v['status'] in FORMALIZED and (v['standing'] == 'proved' or (
                    v['standing'] == 'definition' and v['status'].startswith('definition-'))) else 'partial'
            base = {'id': it['id'], 'kind': it['kind'], 'status': status,
                    'note': note_of(it['id'], repo, v, carrying, short, read=read)}
            ext = {'locator': {'physical': pages}, 'provenance': provenance(v, repo)}

            def finding_of(r):
                return {'verdict': 'deviation', 'status': 'unconfirmed', 'note': r['note']} if confirmed else None
            if verdicts:
                ext['verdicts'] = verdicts
            def make(rel, ends, own=None):
                r = dict(base)
                if own is not None:
                    r['note'] = note_of(it['id'], repo, v, carrying, short, own, read)
                if rel:
                    r['relation'] = rel
                return dict(r, subject=subject, object=ends, extensions={NS: dict(ext)})
            if v['status'] in ABSENT:
                if not v.get('searched'):
                    sys.exit(f"{it['id']}|{repo}: a checked absence with no recorded search")
                if carrying:
                    sys.exit(f"{it['id']}|{repo}: a checked absence with key declarations")
                p = lean[repo]
                records.append((f'noMatch@{TAG[repo]}', make('noMatch', [
                    {'type': 'lean', 'uri': p['repository'], 'version': p['commit']}])))
                counts[f'{repo}.checked_absences'] += 1
            elif not carrying:
                sys.exit(f"{it['id']}|{repo}: status {v['status']} with no key declaration")
            elif relation == 'hasPart':
                for l in carrying:
                    r = make(relation, [], l)
                    r['object'] = [lean_end(l, l['role'], repo, finding_of(r))]
                    records.append((f"{l['role']}__{l['decl']}@{TAG[l.get('repo', repo)]}", r))
            elif len(carrying) == 1:
                l = carrying[0]
                r = make(relation, [])
                r['object'] = [lean_end(l, l['role'], repo, finding_of(r))]
                records.append((f"{l['role']}__{l['decl']}@{TAG[l.get('repo', repo)]}", r))
            else:
                role = carrying[0]['role']
                r = make(relation, [])
                r['object'] = [lean_end(l, l['role'], repo, finding_of(r)) for l in carrying]
                records.append((f"{role}@{TAG[carrying[0].get('repo', repo)]}", r))
            for l in rest:
                records.append((f"{l['role']}__{l['decl']}@{TAG[l.get('repo', repo)]}",
                                make('relatedMatch', [lean_end(l, l['role'], repo)], l)))
            counts[f"{repo}.status.{v['status']}"] += 1
            if confirmed:
                counts[f'{repo}.confirmed_findings'] += 1
        folder = f"{it['section']}/{file_name(it['id'])}"
        keys = [k for k, _ in records]
        names = [file_name(k, '.json') for k in keys]
        clash = collections.Counter(n.lower() for n in names)
        names = [file_name(k, '.json', force_hash=clash[n.lower()] > 1) for k, n in zip(keys, names)]
        if len({n.lower() for n in names}) != len(names):
            sys.exit(f"{it['id']}: two records share a file name")
        for n, (_, r) in zip(names, records):
            p = f'{folder}/{n}'
            if p.lower() in {q.lower() for q in files}:
                sys.exit(f'two files named {p}')
            files[p] = r
            counts['records'] += 1
            counts[f"relation.{r.get('relation', 'none')}"] += 1
        counts['items'] += 1
    with open(os.path.join(out_dir, '_defaults.json'), 'w', encoding='utf-8') as f:
        json.dump(defaults, f, indent=2, ensure_ascii=False)
        f.write('\n')
    for p, r in sorted(files.items()):
        path = os.path.join(out_dir, *p.split('/'))
        os.makedirs(os.path.dirname(path), exist_ok=True)
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(r, f, indent=2, ensure_ascii=False)
            f.write('\n')
    print(json.dumps(dict(sorted(counts.items())), indent=1))


if __name__ == '__main__':
    main()
