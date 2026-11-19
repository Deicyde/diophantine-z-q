"""The standing of a link and of a verdict (docs/taxonomy.md, *Standing*), from data/mapping.json.

A link's declaration standing is the index's. A proved theorem is `conditional` when it assumes a
named Prop that its repository does not prove outright; the Props each repository does prove
outright, by a theorem with no hypotheses and no `sorry`, are DISCHARGED.

A verdict's standing comes from its carrying declarations (the key links; for an [N] verdict
carried by its dependency, the dependency's links). For `parts`, and for a verdict carried by the
dependency, each carrying link is one claim of the item, so the verdict takes the weakest standing
among them; otherwise each key states the whole item, so it takes the strongest. Definitions among
the carrying links do not count. A `definition-*` verdict keeps its recorded `definition` or
`proved` unless one of its carrying theorems is weaker than proved.

Usage: python3 -I scripts/mapping/standing.py [--write] [<repository root>]
  prints every verdict whose recorded standing differs from the rule; --write records the rule's.
"""
import json
import os
import sys

# Props proved outright, per repository of a link (`repo`), with the theorem that proves each.
DISCHARGED = {
    'fork': {'ZInQ.Compiler.NodeCheck.HaltingAddMulBound': 'ZInQ.Compiler.NodeCheck.haltingAddMulBound',
             'ZInQ.MordellWeilE': 'ZInQ.mordellWeilE',
             'ZInQ.CatalogueBound8': 'ZInQ.catalogueBound8',
             'ZInQ.Manuscript.PoleS12.KummerSelmerM': 'ZInQ.Manuscript.PoleS12.kummerSelmerM'},
    'ndep': {'ZInQ.Compiler.NodeCheck.HaltingAddMulBound': 'ZInQ.Compiler.NodeCheck.haltingAddMulBound',
             'ZInQ.MordellWeilE': 'ZInQ.mordellWeilE',
             'ZInQ.CatalogueBound8': 'ZInQ.catalogueBound8'},
    'nasqret': {},
}
# Props a repository proves only from others: named beside them so a note gives the root hypotheses.
# [F]: ZInQ.Mult.multiplication_exact (Multiplication/Top/Exact.lean:26). [N]:
# ZOverQ.Qualitative.multiplication_exact (bounded/QualitativeMultiplication.lean:78), for its own T.
REDUCES = {
    'fork': {'ZInQ.Translation.MultiplicationExact': ('ZInQ.SixContactMin', 'ZInQ.PoleCompleteness',
                                                      'ZInQ.Mult.SlopeRepresentation')},
    'ndep': {'ZInQ.Translation.MultiplicationExact': ('ZInQ.SixContactMin', 'ZInQ.PoleCompleteness',
                                                      'ZInQ.Mult.SlopeRepresentation')},
    'nasqret': {},
}
ORDER = ('proved', 'conditional', 'assumed', 'sorry')  # strongest first


def open_assumes(l, repo):
    """The named Props a link assumes that its repository does not prove outright."""
    lrepo = l.get('repo', repo)
    return [a for a in l['assumes'] if a not in DISCHARGED[lrepo]]


def link_standing(l, repo):
    if l['standing'] == 'proved':
        return 'conditional' if open_assumes(l, repo) else 'proved'
    return l['standing']


def carrying(v):
    """The links that carry a verdict, in the producer's order."""
    if v.get('via_dependency'):
        return sorted((l for l in v['lean'] if l.get('repo') == 'ndep'), key=lambda l: l['decl'])
    return sorted((l for l in v['lean'] if l['role'] == 'key'), key=lambda l: l['decl'])


def verdict_standing(v, repo):
    keys = carrying(v)
    if not keys:
        return 'none'
    got = [s for s in (link_standing(l, repo) for l in keys) if s != 'definition']
    if v['status'].startswith('definition-'):
        worst = max(got, key=ORDER.index) if got else 'proved'
        return v['standing'] if worst == 'proved' and v['standing'] in ('definition', 'proved') else worst
    if not got:
        return 'definition'
    pick = max if v['status'] == 'parts' or v.get('via_dependency') else min
    return pick(got, key=ORDER.index)


def main():
    args = sys.argv[1:]
    write = args[:1] == ['--write']
    args = args[1:] if write else args
    root = args[0] if args else os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    path = os.path.join(root, 'data', 'mapping.json')
    m = json.load(open(path, encoding='utf-8'))
    n = 0
    for rec in m['items']:
        for repo in ('fork', 'nasqret'):
            v = rec[repo]
            if v['status'] in ('no-match', 'not-formalized-not-needed', 'unclear'):
                continue
            s = verdict_standing(v, repo)
            if s != v['standing']:
                n += 1
                print(f"{repo}\t{rec['id']}\t{v['status']}\t{v['standing']} -> {s}")
                v['standing'] = s
    print(f'{n} verdicts differ', file=sys.stderr)
    if write:
        with open(path, 'w', encoding='utf-8') as f:
            json.dump(m, f, indent=1, ensure_ascii=False)
            f.write('\n')


if __name__ == '__main__':
    main()
