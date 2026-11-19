#!/usr/bin/env python3
"""Compare mapper and verifier outputs of batches; list the verdicts a judge must decide.

  compare.py <batch>...   prints one line per item and repository: AGREE or DISAGREE with the
                          reason, and writes scratch/compare/<batch>.json

Two outputs agree on a verdict when they give the same status (definition-match counting as
exact, definition-close as close, definition-differs as differs), the same verdict standing, and
key declarations that overlap (or both have none). For an [N] verdict carried by the dependency,
its ndep support links count as its keys.
"""
import json, os, sys
HOME = os.environ.get('ZQ_WORK') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
S = f'{HOME}/scratch'
REPOS = ('fork', 'nasqret')
NORM = {'definition-match': 'exact', 'definition-close': 'close', 'definition-differs': 'differs'}


def load(kind, b):
    p = f'{S}/{kind}/{b}.json'
    if not os.path.exists(p):
        return None
    return {i['id']: i for i in json.load(open(p))['items']}


def norm(st):
    return NORM.get(st, st)


def keys(v):
    ls = v.get('lean', [])
    if v.get('via_dependency'):
        return sorted({'ndep:' + l['decl'] for l in ls if l.get('repo') == 'ndep'})
    return sorted({l['decl'] for l in ls if l.get('role') == 'key'})


def compare(b):
    m, v = load('map', b), load('verify', b)
    if m is None or v is None:
        print(f'{b}: missing ' + ' '.join(k for k, x in (('map', m), ('verify', v)) if x is None))
        return None
    ids = json.load(open(f'{HOME}/repo/data/batches.json'))
    ids = next(x['items'] for x in ids['batches'] if x['id'] == b)
    res = {}
    for i in ids:
        for repo in REPOS:
            a, c = (m.get(i) or {}).get(repo), (v.get(i) or {}).get(repo)
            k = f'{i}|{repo}'
            if a is None or c is None:
                res[k] = {'agree': False, 'why': 'missing in ' + ('mapper' if a is None else 'verifier')}
                continue
            why = []
            if norm(a['status']) != norm(c['status']):
                why.append(f"status {a['status']} vs {c['status']}")
            if a.get('standing') != c.get('standing'):
                why.append(f"standing {a.get('standing')} vs {c.get('standing')}")
            ka, kc = set(keys(a)), set(keys(c))
            if (ka or kc) and not (ka & kc):
                why.append(f'keys {keys(a)} vs {keys(c)}')
            res[k] = {'agree': not why, 'why': '; '.join(why),
                      'keys_equal': ka == kc,
                      'mapper': {'status': a['status'], 'standing': a.get('standing'), 'keys': keys(a)},
                      'verifier': {'status': c['status'], 'standing': c.get('standing'), 'keys': keys(c)}}
    os.makedirs(f'{S}/compare', exist_ok=True)
    json.dump(res, open(f'{S}/compare/{b}.json', 'w'), indent=1, ensure_ascii=False)
    for k, r in res.items():
        print(f"{b}  {'AGREE   ' if r['agree'] else 'DISAGREE'}  {k}  {r['why']}")
    return res


if __name__ == '__main__':
    for b in sys.argv[1:]:
        compare(b)
