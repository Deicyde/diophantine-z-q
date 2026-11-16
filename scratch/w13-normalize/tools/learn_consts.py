"""Learn declaring modules of erase-guard names the static index cannot see (auto-named instances,
`@[simps]` lemmas, instance-valued structure fields) from the old compile receipts (offline tool).

Observation: in an old receipt file G (rc 0, line-aligned with the staged source), an erase-guard name was
either erased (it resolved, so its declaring module lies in G's import closure) or skipped (it did not).
For each name the static model misses, the candidate declaring modules are the staged modules that
  * lie in the import closure of every file where the name was erased,
  * lie in no import closure of a file where it was skipped,
  * register the name's parent namespace (FLT-prefixed) in the static index.
The most upstream consistent candidate is recorded as owner of `ZInQ.Contrib.CloudW03NeronSurj.FLT.<name>`.
Output: work/learned_consts.json  {name: {owner, candidates, n_pos, n_neg}}.  Diagnostic facts only.
"""
import os, sys, json, collections
sys.path.insert(0, os.path.dirname(__file__))
import validate_erase as ve
from sim import Graph, PREFIX
from index import split_name
from graph import mod_of, path_of

WORK = '/home/jackmccarthy/cloud-b3/w13/normalize/work'


def main():
    G = Graph()
    latest = ve.load_receipts()
    pos = collections.defaultdict(set)
    neg = collections.defaultdict(set)
    missed = set()
    for f, (k, rc, d) in sorted(latest.items()):
        if rc != 0:
            continue
        mod = mod_of(f)
        mp = os.path.join(WORK, 'full_manifest', mod + '.json')
        if not os.path.exists(mp):
            continue
        man = json.load(open(mp))
        decs = [x for x in man['decisions'] if 'attr' in x]
        if not decs:
            continue
        skips = ve.receipt_skips(d)
        lines_with_dec = set((x['line'], x['attr']) for x in decs)
        if any(key not in lines_with_dec for key in skips):
            continue
        for x in decs:
            actual = x['name'] not in skips.get((x['line'], x['attr']), set())
            if actual:
                pos[x['name']].add(mod)
            else:
                neg[x['name']].add(mod)
            if actual and not x['erase']:
                missed.add(x['name'])
    out = {}
    order = {}
    for i, m in enumerate(sorted(G.idx)):
        order[m] = len(G.staged_closure(m)[0])
    for n in sorted(missed):
        full = PREFIX + '.' + n
        par = '.'.join(split_name(full)[:-1])
        cand = None
        for g in pos[n]:
            sc = G.staged_closure(g)[0] | {g}
            cand = set(sc) if cand is None else cand & sc
        cand = cand or set()
        for g in neg[n]:
            sc = G.staged_closure(g)[0] | {g}
            cand -= sc
        cand_ns = [m for m in cand if par in G.idx[m].ns]
        pick = sorted(cand_ns or cand, key=lambda m: order[m])
        out[n] = {'full': full, 'owner': pick[0] if pick else None, 'candidates': len(cand), 'ns_candidates': len(cand_ns),
                  'n_pos': len(pos[n]), 'n_neg': len(neg[n])}
    json.dump(out, open(os.path.join(WORK, 'learned_consts.json'), 'w'), indent=1)
    c = collections.Counter('owner' if v['owner'] else 'none' for v in out.values())
    amb = sum(1 for v in out.values() if v['ns_candidates'] > 1)
    print(len(out), c, 'ambiguous(ns candidates>1):', amb)


if __name__ == '__main__':
    main()
