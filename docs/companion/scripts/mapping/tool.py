#!/usr/bin/env python3
"""Lookup tool for the mapping campaign: items, batches, Lean declarations, checks.

Repositories: fork ([F]), nasqret ([N]), ndep ([N]'s kernel dependency).

  tool.py batch <B>                 items of a batch: kind, lines, LaTeX, seeds
  tool.py item <id> [ctx]           one item with <ctx> manuscript lines around it (default 8)
  tool.py tex <a> <b>               manuscript lines a..b
  tool.py decl <repo> <name> [n]    index row of a declaration and n source lines (default 40)
  tool.py search <repo> <regex> [--snippet] [--vendored] [--limit N]
                                    declarations whose name (or statement snippet) matches
  tool.py exists <repo> <name>...   check names against the repository's index
  tool.py headlines                 the headline theorems and assumed hypotheses of each repository
  tool.py check <json>              validate a mapper/verifier/judge output file
"""
import json, os, re, sys

HOME = os.environ.get('ZQ_WORK') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
REPO = f'{HOME}/repo'
TEX = f'{HOME}/m/diophantine_zq.tex'
BATCHES = f'{REPO}/data/batches.json'
SRC = {'fork': f'{HOME}/fork', 'nasqret': f'{HOME}/nasqret', 'ndep': f'{HOME}/ndep'}
INDEX = {'fork': f'{HOME}/scratch/decls-fork.json', 'nasqret': f'{REPO}/data/decls-nasqret.json',
         'ndep': f'{HOME}/scratch/decls-ndep.json'}

STATUSES = {
    'exact', 'close', 'stronger', 'weaker', 'differs', 'missing-hypothesis', 'parts',
    'inlined', 'definition-match', 'definition-close', 'definition-differs',
    'not-formalized-not-needed', 'no-match', 'unclear',
}
NO_KEY = {'no-match', 'not-formalized-not-needed', 'unclear'}
ROLES = {'key', 'attributed', 'support', 'helper'}
STANDINGS = {'proved', 'assumed', 'definition', 'sorry'}
VERDICT_STANDINGS = {'proved', 'conditional', 'assumed', 'definition', 'sorry', 'none'}
REPOS = ('fork', 'nasqret')

_idx = {}


def index(repo):
    if repo not in _idx:
        d = json.load(open(INDEX[repo]))
        rows = {}
        for r in d['declarations']:
            rows.setdefault(r['name'], []).append(r)
        _idx[repo] = (d, rows)
    return _idx[repo]


def rows(repo):
    return index(repo)[1]


def items():
    its = json.load(open(f'{REPO}/data/items.json'))['items']
    return {i['id']: i for i in its}


def texts():
    return json.load(open(f'{HOME}/scratch/items-text.json'))


def seeds():
    return json.load(open(f'{REPO}/data/seeds.json'))['items']


def lines_of(it):
    return ', '.join(f'{a}-{b}' for a, b in it['lines'])


def show_seeds(s):
    f = s.get('fork', {})
    for p in f.get('blueprint', []):
        ds = ', '.join(f"{d['name']} [{d['standing']}]" for d in p.get('declarations', []))
        print(f"    [F] blueprint {p['page']} ({p['lines']}): {p['title']}" + (f' -> {ds}' if ds else ''))
    lex = f.get('lexical', [])
    if lex:
        print(f"    [F] lexical ({f.get('lexical_total', len(lex))} total): " +
              ', '.join(f"{d['name']} [{d['standing']}]" for d in lex[:12]))
    n = s.get('nasqret', {})
    for e in n.get('blueprint', []):
        print(f"    [N] blueprint entry {e['entry']} {e['kind']} '{e['title']}' ({e['section_file']}, score {e['score']})"
              f" -> {e.get('declaration')} [{e.get('declaration_repository')}, {e.get('standing')}]")
    vk = n.get('via_kernel', [])
    if vk:
        print(f"    [N] mentions a seeded kernel declaration ({n.get('via_kernel_total', len(vk))} total): " +
              ', '.join(f"{d['name']} [{d['standing']}] (mentions {', '.join(d['mentions'])})" for d in vk[:10]))
    lex = n.get('lexical', [])
    if lex:
        print(f"    [N] lexical ({n.get('lexical_total', len(lex))} total): " +
              ', '.join(f"{d['name']} [{d['standing']}]" for d in lex[:12]))
    if s.get('terms'):
        print(f"    terms: {', '.join(s['terms'])}")


def show_item(it, tx, sd, ctx=None):
    print(f"=== {it['id']}  ({it['kind']}{', label ' + it['label'] if it.get('label') else ''})"
          f"  lines {lines_of(it)}  section {it['section']}" +
          (f"  enclosing: {it['enclosing']}" if it.get('enclosing') else ''))
    if ctx:
        lines = open(TEX).read().split('\n')
        for a, b in it['lines']:
            for i in range(max(1, a - ctx), min(len(lines), b + ctx) + 1):
                print(f'    {i:5d}| {lines[i-1]}')
    else:
        print('    LaTeX:')
        for l in tx.get(it['id'], '').split('\n'):
            print('      ' + l)
    show_seeds(sd.get(it['id'], {}))


def cmd_batch(b):
    bs = json.load(open(BATCHES))['batches']
    ids = next(x['items'] for x in bs if x['id'] == b)
    by, tx, sd = items(), texts(), seeds()
    print(f'batch {b}: {len(ids)} items: ' + '; '.join(ids))
    for i in ids:
        show_item(by[i], tx, sd)
        print()


def cmd_item(i, ctx=8):
    show_item(items()[i], texts(), seeds(), ctx=int(ctx))


def cmd_tex(a, b):
    lines = open(TEX).read().split('\n')
    for i in range(int(a), min(int(b), len(lines)) + 1):
        print(f'{i:5d}| {lines[i-1]}')


def resolve(repo, name):
    R = rows(repo)
    if name in R:
        return name
    cands = [k for k in R if k.endswith('.' + name)]
    return cands[0] if len(cands) == 1 else cands


def cmd_decl(repo, name, n=40):
    r = resolve(repo, name)
    if isinstance(r, list):
        print(f'{name}: NOT FOUND in {repo}' + (f'; candidates: {r[:20]}' if r else ''))
        return
    if r != name:
        print(f'(resolved {name} -> {r})')
    for row in rows(repo)[r]:
        flags = ' '.join(k for k in ('vendored', 'private', 'duplicate', 'prop') if row.get(k))
        print(f"{row['name']}  [{row['kind']}]  {repo}:{row['file']}:{row['line']}  standing {row['standing']}"
              + (f"  assumed_by {row['assumed_by']}" if row.get('assumed_by') else '') + (f'  ({flags})' if flags else ''))
    row = rows(repo)[r][0]
    lines = open(f"{SRC[repo]}/{row['file']}", errors='replace').read().split('\n')
    a = row['line']
    s = a
    while s > 1 and a - s < 25 and (lines[s-2].strip().startswith(('/--', '-/', '--', '@[')) or
                                    ('/--' in '\n'.join(lines[max(0, s-26):s-1]) and '-/' not in lines[s-2] and lines[s-2].strip())):
        s -= 1
    if s > 1 and lines[s-2].strip().endswith('-/'):
        while s > 1 and a - s < 40 and '/--' not in lines[s-1]:
            s -= 1
    for i in range(s, min(len(lines), a + int(n)) + 1):
        print(f'{i:5d}| {lines[i-1]}')


def cmd_search(repo, *args):
    args = list(args)
    snip = '--snippet' in args
    vend = '--vendored' in args
    lim = 60
    if '--limit' in args:
        j = args.index('--limit'); lim = int(args[j+1]); del args[j:j+2]
    args = [a for a in args if a not in ('--snippet', '--vendored')]
    rx = re.compile(args[0])
    k = 0
    for name, rs in rows(repo).items():
        r = rs[0]
        if r.get('vendored') and not vend:
            continue
        if rx.search(name) or (snip and r.get('snippet') and rx.search(r['snippet'])):
            print(f"{name}  [{r['kind']}, {r['standing']}]  {r['file']}:{r['line']}")
            k += 1
            if k >= lim:
                print(f'... (limit {lim})'); break


def cmd_exists(repo, *names):
    R = rows(repo)
    for n in names:
        if n in R:
            r = R[n][0]
            print(f"OK  {n}  {r['file']}:{r['line']}  {r['standing']}")
        else:
            print('MISSING ' + n)


def cmd_headlines():
    for repo in ('fork', 'nasqret'):
        d = index(repo)[0]
        print(f'[{repo}] headlines:')
        for h in d.get('headlines', []):
            print(f"  {h['name']}  {h['file']}:{h['line']}  hypotheses: {', '.join(h['hypotheses'])}")
        ass = sorted(n for n, rs in rows(repo).items() if rs[0]['standing'] == 'assumed')
        print(f'  assumed ({len(ass)}): ' + ', '.join(ass))
        if d.get('assumed_in_dependency'):
            print(f"  assumed in the dependency: {d['assumed_in_dependency']}")


def standing_of(repo, name):
    rs = rows(repo).get(name)
    return rs[0]['standing'] if rs else None


def check_verdict(iid, repo, v, errs):
    p = f'{iid} [{repo}]'
    if not isinstance(v, dict):
        errs.append(f'{p}: no verdict'); return
    st = v.get('status')
    if st not in STATUSES:
        errs.append(f'{p}: bad status {st}')
    if not v.get('note'):
        errs.append(f'{p}: no note')
    if v.get('standing') not in VERDICT_STANDINGS:
        errs.append(f'{p}: bad verdict standing {v.get("standing")}')
    keys = []
    for l in v.get('lean', []):
        n, role = l.get('decl'), l.get('role')
        lrepo = l.get('repo', repo)
        if role not in ROLES:
            errs.append(f'{p}: bad role {role} for {n}')
        if repo == 'fork' and lrepo != 'fork':
            errs.append(f'{p}: a fork verdict names {lrepo} declaration {n}')
        if repo == 'nasqret' and lrepo not in ('nasqret', 'ndep'):
            errs.append(f'{p}: bad repo {lrepo} for {n}')
        if lrepo == 'ndep' and role != 'support':
            errs.append(f'{p}: dependency declaration {n} must have role support')
        s = standing_of(lrepo, n) if lrepo in INDEX else None
        if s is None:
            errs.append(f'{p}: declaration not found in {lrepo}: {n}')
        elif l.get('standing') != s:
            errs.append(f'{p}: standing of {n} is {s} in the index, not {l.get("standing")}')
        for h in l.get('assumes', []):
            if standing_of(lrepo, h) is None and standing_of('ndep', h) is None:
                errs.append(f'{p}: assumed hypothesis not found: {h}')
        if role == 'key':
            keys.append(l)
    if st in ('no-match', 'not-formalized-not-needed') and not v.get('searched'):
        errs.append(f'{p}: status {st} without searched')
    via = repo == 'nasqret' and v.get('via_dependency')
    if via and (keys or not any(l.get('repo') == 'ndep' for l in v.get('lean', []))):
        errs.append(f'{p}: via_dependency needs ndep support links and no key')
    if st not in NO_KEY and not keys and not via:
        errs.append(f'{p}: status {st} without a key declaration')
    if st in NO_KEY and keys and st != 'no-match':
        errs.append(f'{p}: status {st} with a key declaration')
    if st == 'no-match' and v.get('standing') != 'none':
        errs.append(f'{p}: no-match needs verdict standing none')


def cmd_check(path):
    d = json.load(open(path))
    errs = []
    its = d.get('items', [])
    if not its:
        errs.append('no items')
    for it in its:
        iid = it.get('id')
        for repo in REPOS:
            if repo in it or 'judge' not in path:
                check_verdict(iid, repo, it.get(repo), errs)
    if 'batch' in d and os.path.exists(BATCHES) and '/judge/' not in path:
        bs = json.load(open(BATCHES))['batches']
        want = next((x['items'] for x in bs if x['id'] == d['batch']), None)
        got = [i.get('id') for i in its]
        if want is not None and sorted(got) != sorted(want):
            errs.append(f'items {got} != batch {want}')
    print('\n'.join(errs) if errs else f'OK {path}: {len(its)} items')
    return 1 if errs else 0


if __name__ == '__main__':
    if len(sys.argv) < 2 or sys.argv[1] in ('-h', 'help', '--help'):
        print(__doc__); sys.exit(0)
    sys.exit(globals()['cmd_' + sys.argv[1]](*sys.argv[2:]) or 0)
