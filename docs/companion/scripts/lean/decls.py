#!/usr/bin/env python3
"""Declaration index of one Lean repository from its source text at its pin (nothing is built).

Adapted from ym-companion's scripts/lean/decls.py, over formal-companion's adapters:
`leanparse.parse_file` gives every declaration with its keyword, namespace, modifiers and body;
`leansnippets.index_text` gives the statement snippet (a theorem's statement through the `:=` of its
proof, a definition whole, capped) and structure fields.  A command indented or behind a same-line
`open ... in` prefix is given to the parsers with the prefix removed (line numbers are kept).

Each row: name, kind, module, file, line, snippet, vendored, prop (a def/abbrev/structure/class whose
type is `Prop`), sorry (its own text, comments removed, contains `sorry` or `admit`), standing.
Standing: a theorem or lemma is `proved` when its proof has no `sorry`, else `sorry`; a definition
(also `irreducible_def`) is `definition`, or `sorry` when its body has one; an `axiom` is `axiom`; an
`alias` takes its target's standing (`proved` when the target is not found and it has no `sorry`).  `assumed` is set afterwards
by standing.py.

Usage: python3 -I decls.py <fc dir> <repo dir> <repo url> <commit> <out json> <dir or file>[,...]
       [--vendored <path component>,...] [--skip <path component>,...]
"""
import json
import os
import re
import sys
from multiprocessing import Pool

FC = sys.argv[1]
sys.path.insert(0, os.path.join(FC, 'scripts'))
from adapters import leanparse, leansnippets  # noqa: E402

KW = r'(?:theorem|lemma|def|abbrev|irreducible_def|alias|structure|class|inductive|instance|example|opaque|axiom|namespace|end|section|mutual)'
MOD = r'(?:@\[[^\]]*\]\s*|(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped|local|public|meta)\s+)*'
PREFIX = re.compile(r'^(?:\s*(?:omit|include|open|set_option|variable)\b[^\n]*?\bin\s+)+(?=' + MOD + KW + r'\b)')
INDENT = re.compile(r'^[ \t]+(?=' + MOD + KW + r'\b)')
KINDS = leanparse.DEFAULT_DECL_KINDS + ('irreducible_def', 'alias')
SORRY = re.compile(r'(?<![\w.\'])(sorry|admit)(?![\w\'])')
STRING = re.compile(r'"(?:[^"\\\n]|\\.)*"')


def normalize(text):
    lines = text.split('\n')
    depths = leanparse.comment_depths(lines)
    for i, line in enumerate(lines):
        if not depths[i]:
            lines[i] = INDENT.sub('', PREFIX.sub('', line))
    return '\n'.join(lines)


def module_of(rel):
    return rel[:-5].replace('/', '.')


def is_prop(kind, snippet):
    """The declared type is `Prop`: `def P ... : Prop :=`, `structure P ... : Prop where`."""
    head = snippet
    if kind in ('def', 'abbrev'):
        lines = snippet.split('\n')
        ps = leansnippets.proof_start(lines, 0, len(lines))
        if not ps:
            return False
        head = '\n'.join(lines[:ps[0]] + [lines[ps[0]][:ps[1]]])
        return re.search(r':\s*Prop\s*$', leanparse.strip_comments(head)) is not None
    if kind in ('structure', 'class'):
        first = re.split(r'\bwhere\b|:=|\bextends\b', leanparse.strip_comments(snippet), maxsplit=1)[0]
        return re.search(r':\s*Prop\s*$', first.strip()) is not None or \
            re.search(r'^[^\n]*:\s*Prop\b', leanparse.strip_comments(snippet).split('where')[0]) is not None
    return False


def index_file(args):
    root, rel, vendored = args
    try:
        text = normalize(open(os.path.join(root, rel), encoding='utf-8').read())
    except UnicodeDecodeError:
        return rel, [], 'not utf-8'
    tmp = f'/tmp/decls-{os.getpid()}.lean'
    open(tmp, 'w', encoding='utf-8').write(text)
    try:
        decls = leanparse.parse_file(tmp, rel=rel, decl_kinds=KINDS)
        snips = leansnippets.index_text(text)
    except Exception as e:      # a file the parsers cannot read is reported, not skipped silently
        return rel, [], f'{type(e).__name__}: {e}'
    rows = []
    seen = set()
    for d in decls:
        sn = snips.get(d.full_name)
        snippet = sn[1] if sn and sn[0] == d.line else leanparse.signature(d.body)
        own = STRING.sub('""', leanparse.strip_comments(d.body))
        has_sorry = SORRY.search(own) is not None
        kind = d.kind
        if kind in ('theorem', 'lemma'):
            standing = 'sorry' if has_sorry else 'proved'
        elif kind == 'axiom':
            standing = 'axiom'
        elif kind == 'alias':
            standing = 'alias'          # resolved to its target's standing below
        elif kind == 'example':
            standing = 'sorry' if has_sorry else 'proved'
        else:
            standing = 'sorry' if has_sorry else 'definition'
        rows.append({'name': d.full_name, 'kind': kind, 'module': module_of(rel), 'file': rel, 'line': d.line,
                     'snippet': snippet[:4000], 'vendored': vendored, 'private': d.private,
                     'prop': is_prop(kind, snippet), 'sorry': has_sorry, 'standing': standing})
        seen.add(d.full_name)
    for name, (line, snippet) in snips.items():
        if name not in seen:
            rows.append({'name': name, 'kind': 'field', 'module': module_of(rel), 'file': rel, 'line': line,
                         'snippet': snippet[:4000], 'vendored': vendored, 'private': False, 'prop': False,
                         'sorry': False, 'standing': 'definition'})
    os.remove(tmp)
    return rel, rows, None


def main():
    root, url, commit, out = sys.argv[2:6]
    targets = sys.argv[6].split(',')
    opts = dict(zip(sys.argv[7::2], sys.argv[8::2]))
    vend = set(filter(None, opts.get('--vendored', '').split(',')))
    skip = set(filter(None, opts.get('--skip', '').split(',')))
    files = []
    for t in targets:
        p = os.path.join(root, t)
        if os.path.isfile(p):
            files.append(t)
            continue
        for d, dirs, fs in os.walk(p):
            dirs[:] = sorted(x for x in dirs if x not in ('.lake', '.git') and x not in skip)
            files += [os.path.relpath(os.path.join(d, f), root) for f in sorted(fs) if f.endswith('.lean')]
    files = sorted(set(files))
    jobs = [(root, rel, any(c in vend for c in rel.split('/')[:-1])) for rel in files]
    rows, errors = [], {}
    with Pool(12) as pool:
        for rel, rs, err in pool.imap(index_file, jobs, chunksize=20):
            rows += rs
            if err:
                errors[rel] = err
    by_name = {r['name']: r for r in rows}
    for r in rows:
        if r['kind'] == 'alias':
            m = re.search(r':=\s*@?([A-Za-z_][\w\'.!?]*)', r['snippet'])
            ns = r['name'].split('.')[:-1]
            tgt = None
            for k in range(len(ns), -1, -1):
                cand = '.'.join(ns[:k] + [m.group(1)]) if m else None
                if cand in by_name and by_name[cand]['kind'] != 'alias':
                    tgt = by_name[cand]
                    break
            r['alias_of'] = tgt['name'] if tgt else None
            r['standing'] = tgt['standing'] if tgt else ('sorry' if r['sorry'] else 'proved')
    names = {}
    for r in rows:
        names[r['name']] = names.get(r['name'], 0) + 1
    for r in rows:
        r['duplicate'] = names[r['name']] > 1
    json.dump({'repository': url, 'commit': commit, 'targets': targets, 'vendored_components': sorted(vend),
               'skipped_components': sorted(skip), 'files': len(files), 'unreadable': errors,
               'declarations': rows}, open(out, 'w', encoding='utf-8'), ensure_ascii=False)
    print(json.dumps({'files': len(files), 'rows': len(rows), 'unreadable': len(errors)}))


if __name__ == '__main__':
    main()
