#!/usr/bin/env python3
"""Counts of data/mapping.json for the report: statuses, standings, judges' rulings, findings.

  stats.py            prints markdown tables
  stats.py findings   prints the findings, confirmed and not, one line each
"""
import collections, glob, json, os, sys
REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
S = os.path.join(os.path.dirname(REPO), 'scratch')  # the campaign's scratch tree, for the judges' rulings only

m = json.load(open(f'{REPO}/data/mapping.json'))['items']
REPOS = ('fork', 'nasqret')
STATUS_ORDER = ['exact', 'close', 'stronger', 'parts', 'inlined', 'definition-match', 'definition-close',
                'weaker', 'missing-hypothesis', 'differs', 'definition-differs', 'no-match',
                'not-formalized-not-needed', 'unclear']
STAND_ORDER = ['proved', 'conditional', 'assumed', 'definition', 'sorry', 'none']


def table(title, key, order, subset=lambda r: True):
    c = {repo: collections.Counter(r[repo].get(key) for r in m if subset(r) and r[repo].get('judged'))
         for repo in REPOS}
    print(f'\n{title}\n\n| {key} | [F] | [N] |\n| --- | --- | --- |')
    for k in order:
        if c['fork'][k] or c['nasqret'][k]:
            print(f"| `{k}` | {c['fork'][k]} | {c['nasqret'][k]} |")
    print(f"| total | {sum(c['fork'].values())} | {sum(c['nasqret'].values())} |")


def findings():
    for r in m:
        for repo in REPOS:
            v = r[repo]
            ver = v.get('verification', {})
            f = ver.get('finding')
            if f:
                tag = '[F]' if repo == 'fork' else '[N]'
                keys = [l['decl'] for l in v.get('lean', []) if l['role'] == 'key'] or \
                       [l['decl'] for l in v.get('lean', []) if l.get('repo') == 'ndep']
                print(f"{f}\t{r['id']}\t{tag}\t{ver.get('claimed')}->{v['status']}\t{', '.join(keys[:3])}\t{v['note']}")


def rulings():
    if not os.path.isdir(f'{S}/judge'):
        return
    c = collections.Counter()
    for p in glob.glob(f'{S}/judge/*.json'):
        post = p.endswith('-post.json')
        for it in json.load(open(p))['items']:
            for repo, rr in (it.get('ruling') or {}).items():
                c[('post-skeptic' if post else 'judge', rr.get('for'))] += 1
    print('\n| step | ruled for | verdicts |\n| --- | --- | --- |')
    for (k, f), n in sorted(c.items()):
        print(f'| {k} | {f} | {n} |')


if __name__ == '__main__':
    if sys.argv[1:] == ['findings']:
        findings()
    else:
        kinds = {'statement': ('theorem', 'proposition', 'lemma', 'definition', 'corollary', 'remark')}
        table('All 330 items, by status', 'status', STATUS_ORDER)
        table('All 330 items, by standing', 'standing', STAND_ORDER)
        table('The 71 numbered statements, by status', 'status', STATUS_ORDER,
              lambda r: r['kind'] in kinds['statement'])
        table('The 71 numbered statements, by standing', 'standing', STAND_ORDER,
              lambda r: r['kind'] in kinds['statement'])
        rulings()
        ver = collections.Counter()
        for r in m:
            for repo in REPOS:
                v = r[repo].get('verification', {})
                ver['agree' if v.get('mapper_verifier_agree') else 'disagree'] += 1
                for k in ('finding', 'absence'):
                    if k in v:
                        ver[(k, v[k])] += 1
        print('\n' + '\n'.join(f'- {k}: {n}' for k, n in sorted(ver.items(), key=str)))
