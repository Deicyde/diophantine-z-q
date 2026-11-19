#!/usr/bin/env python3
"""Harvest one repository's blueprint into link records.

For every page under blueprint/roadmap/ that names Lean declarations and whose
"## Sources" list points at a manuscript-backed locator section, emit one record:
the manuscript passage (line ranges or a TeX label) and the page's declarations,
each resolved to a file and line in the same checkout.

Usage: harvest.py <checkout> <items.json> <out.json>
"""
import collections
import json
import os
import re
import sys

MS_LINES = 11259
ROOT = sys.argv[1]
ITEMS = json.load(open(sys.argv[2], encoding='utf-8'))
LABELS = {x['label']: x for x in ITEMS}
BP = os.path.join(ROOT, 'blueprint')


def norm(s):
    return re.sub(r'[^a-z0-9]', '', s.lower())


def strip_parens(s):
    prev = None
    while prev != s:
        prev = s
        s = re.sub(r'\([^()]*\)', ' ', s)
    return s


RANGE = r'\d+(?:\s*[-–]\s*\d+)?'
LINES_RE = re.compile(r'\blines?\s+(' + RANGE + r'(?:(?:\s*,\s*|\s*,?\s+and\s+)' + RANGE + r')*)', re.I)


def ranges_in(s):
    out = []
    for m in LINES_RE.finditer(s):
        for a, b in re.findall(r'(\d+)(?:\s*[-–]\s*(\d+))?', m.group(1)):
            a = int(a)
            b = int(b or a)
            if 1 <= a <= b <= MS_LINES:
                out.append((a, b))
    return out


def merge(rs):
    rs = sorted(set(rs))
    out = []
    for a, b in rs:
        if out and a <= out[-1][1] + 1:
            out[-1] = (out[-1][0], max(out[-1][1], b))
        else:
            out.append((a, b))
    return out


def subject_of(body, manuscript_page):
    """Return (how, ranges, label) for one locator section."""
    para = body.strip().split('\n\n')[0].replace('\n', ' ')
    labels = [l for l in re.findall(r'`([a-z]+:[A-Za-z0-9-]+)`', para)]
    if manuscript_page:
        for l in labels:
            if l in LABELS:
                return 'label', [], l
        return None, [], None
    masked = re.sub(r'`[^`]*`', 'LBL', para)
    flat = strip_parens(masked)
    head = re.split(r':(?:\s|$)', flat, maxsplit=1)[0]
    r = ranges_in(head)
    if r:
        return 'head', merge(r), None
    r = ranges_in(flat)
    if r:
        return 'paragraph', merge(r), None
    for l in labels:
        if l in LABELS:
            return 'label', [], l
    r = ranges_in(strip_parens(re.sub(r'`[^`]*`', 'LBL', body.replace('\n', ' '))))
    if r:
        return 'section', merge(r), None
    return None, [], None


def parse_sources():
    out = {}
    d = os.path.join(BP, 'sources')
    for f in sorted(os.listdir(d)):
        if not f.endswith('.md') or f == 'README.md':
            continue
        text = open(os.path.join(d, f), encoding='utf-8').read()
        parts = re.split(r'^## (.+)$', text, flags=re.M)
        header = parts[0]
        is_ms_page = f == 'manuscript.md'
        backed = is_ms_page or bool(re.search(r'Line (?:ranges|numbers) refer to\s+`diophantine_zq\.tex`', header))
        secs = {}
        for i in range(1, len(parts), 2):
            heading = parts[i].strip()
            body = parts[i + 1]
            how, rs, label = subject_of(body, is_ms_page) if backed else (None, [], None)
            secs[norm(heading)] = {'heading': heading, 'how': how, 'ranges': rs, 'label': label}
        out[f] = {'backed': backed, 'sections': secs}
    return out


def parse_node(path):
    t = open(path, encoding='utf-8').read()
    fm = {}
    m = re.match(r'---\n(.*?)\n---\n', t, re.S)
    if m:
        for line in m.group(1).split('\n'):
            if ':' in line:
                k, v = line.split(':', 1)
                fm[k.strip()] = v.strip()
    title = re.search(r'^# (.+)$', t, re.M)
    links = []
    s = re.search(r'\n## Sources\n(.*?)(\n## |\Z)', t, re.S)
    if s:
        for text, target in re.findall(r'\[([^\]]*)\]\(([^)\s]+)\)', s.group(1)):
            links.append((text, target))
    return fm, (title.group(1).strip() if title else ''), links


DECL = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*)*'
    r'(?:(?:private|protected|noncomputable|nonrec|unsafe|partial|public|scoped|local|meta)\s+)*'
    r'(theorem|lemma|def|abbrev|structure|class|inductive|instance|opaque|axiom|irreducible_def|alias)\s+'
    r'([^\s:({\[⦃]+)')


def index_lean():
    idx = collections.defaultdict(list)
    skip_top = {'scratch', 'contrib-upstream', '.lake', '.git', 'build', 'docs', 'blueprint'}
    for top in sorted(os.listdir(ROOT)):
        if top in skip_top:
            continue
        p = os.path.join(ROOT, top)
        files = []
        if os.path.isdir(p):
            for d, dirs, fs in os.walk(p):
                dirs[:] = [x for x in dirs if x not in ('.lake', '.git')]
                files += [os.path.join(d, f) for f in fs if f.endswith('.lean')]
        elif top.endswith('.lean'):
            files = [p]
        for fp in files:
            rel = os.path.relpath(fp, ROOT)
            try:
                lines = open(fp, encoding='utf-8').read().split('\n')
            except UnicodeDecodeError:
                continue
            stack = []
            depth = 0
            for n, line in enumerate(lines, 1):
                code = line
                if depth == 0 and '/-' not in line:
                    pass
                else:
                    buf = []
                    i = 0
                    while i < len(line):
                        two = line[i:i + 2]
                        if two == '/-':
                            depth += 1
                            i += 2
                        elif two == '-/' and depth > 0:
                            depth -= 1
                            i += 2
                        else:
                            if depth == 0:
                                buf.append(line[i])
                            i += 1
                    code = ''.join(buf)
                code = code.split('--')[0]
                s = code.strip()
                if not s:
                    continue
                m = re.match(r'namespace\s+(\S+)', s)
                if m:
                    stack.append(('ns', m.group(1)))
                    continue
                if re.match(r'(?:noncomputable\s+|public\s+)*section(?:\s+\S+)?$', s):
                    stack.append(('sec', None))
                    continue
                if re.match(r'end(?:\s+\S+)?$', s):
                    if stack:
                        stack.pop()
                    continue
                m = DECL.match(code)
                if m:
                    name = m.group(2)
                    if name.startswith('_root_.'):
                        full = name[len('_root_.'):]
                    else:
                        full = '.'.join([x[1] for x in stack if x[0] == 'ns'] + [name])
                    idx[full].append((rel, n, m.group(1)))
    return idx


def module_of(rel):
    if rel.startswith('ZInQKernel/') or rel == 'ZInQKernel.lean':
        return rel[:-5].replace('/', '.')
    if rel.startswith('lean/'):
        return rel[5:-5].replace('/', '.')
    return None


def main():
    sources = parse_sources()
    idx = index_lean()
    by_last = collections.defaultdict(set)
    for full in idx:
        by_last[full.split('.')[-1]].add(full)
    records = []
    stats = collections.Counter()
    unresolved_anchor = []
    for d, _, fs in os.walk(os.path.join(BP, 'roadmap')):
        for f in sorted(fs):
            if not f.endswith('.md') or f == 'README.md':
                continue
            path = os.path.join(d, f)
            rel = os.path.relpath(path, ROOT)
            fm, title, links = parse_node(path)
            stats['pages'] += 1
            names = [x.strip() for x in fm.get('lean', '').split(',') if x.strip()]
            passages = []
            for text, target in links:
                tpath, _, anchor = target.partition('#')
                tfile = os.path.basename(tpath)
                if '/sources/' not in ('/' + os.path.normpath(os.path.join(os.path.dirname(rel), tpath)) + '/').replace('\\', '/') + '/':
                    continue
                src = sources.get(tfile)
                if not src:
                    continue
                if not src['backed']:
                    stats['links to project-note locators'] += 1
                    continue
                sec = src['sections'].get(norm(anchor))
                if sec is None:
                    unresolved_anchor.append((rel, target))
                    continue
                if sec['how'] is None:
                    stats['locator sections without a manuscript span'] += 1
                    continue
                passages.append({'file': tfile, 'anchor': anchor, 'heading': sec['heading'], 'how': sec['how'],
                                 'ranges': sec['ranges'], 'label': sec['label'], 'link_text': text})
            if not passages:
                stats['pages with no manuscript passage'] += 1
                continue
            if not names:
                stats['pages with a manuscript passage but no lean field'] += 1
            decls = []
            for nm in names:
                hits = idx.get(nm)
                how = 'exact'
                if not hits:
                    cands = [c for c in by_last.get(nm.split('.')[-1], ()) if c.endswith('.' + nm) or nm.endswith('.' + c)]
                    if len(cands) == 1:
                        hits = idx[cands[0]]
                        how = 'suffix:' + cands[0]
                if hits:
                    relp, line, kw = hits[0]
                    decls.append({'name': nm, 'path': relp, 'line': line, 'keyword': kw, 'module': module_of(relp),
                                  'resolved': how, 'ambiguous': len(hits) > 1})
                    stats['declarations resolved'] += 1
                else:
                    decls.append({'name': nm, 'path': None, 'line': None, 'keyword': None, 'module': None,
                                  'resolved': None, 'ambiguous': False})
                    stats['declarations not found in source'] += 1
            seen = set()
            for p in passages:
                key = (p['file'], norm(p['anchor']))
                if key in seen:
                    continue
                seen.add(key)
                records.append({'page': rel, 'chapter': rel.split('/')[2], 'title': title,
                                'article_id': fm.get('article_id'), 'origin': fm.get('origin'),
                                'declaration': fm.get('declaration'), 'statement': fm.get('statement'),
                                'proof': fm.get('proof'), 'passage': p, 'decls': decls})
                stats['records'] += 1
    json.dump({'records': records, 'stats': stats, 'unresolved_anchor': unresolved_anchor,
               'sources': {k: {'backed': v['backed'], 'sections': v['sections']} for k, v in sources.items()}},
              open(sys.argv[3], 'w', encoding='utf-8'), indent=1, ensure_ascii=False)
    for k, v in sorted(stats.items()):
        print(f'{v:6d}  {k}')
    print('unresolved anchors:', len(unresolved_anchor), unresolved_anchor[:5])
    print('lean names indexed:', len(idx))


main()
