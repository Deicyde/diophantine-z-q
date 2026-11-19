#!/usr/bin/env python3
"""Merge the campaign's outputs into data/mapping.json.

For each item and repository the verdict is, in order: the post-skeptic judge's
(scratch/judge/<batch>-post.json), the judge's (scratch/judge/<batch>.json), or the mapper's when
the verifier agreed with it (scratch/compare/<batch>.json). A mapper verdict with no verifier is
merged as unverified. `verification` records which steps ran and how they ended.

Findings (stronger, weaker, missing-hypothesis, differs, definition-differs) need two skeptics,
scratch/skeptic/<item>-<repository>-{1,2}.json; a finding is confirmed only if both ran and
neither refuted it. A no-match in Sections 7-9 or Appendices E-H needs one skeptic.
"""
import json, os, re
HOME = os.environ.get('ZQ_WORK') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
S = f'{HOME}/scratch'
REPO = f'{HOME}/repo'
REPOS = ('fork', 'nasqret')
FINDINGS = {'stronger', 'weaker', 'missing-hypothesis', 'differs', 'definition-differs'}
FAR = {'7', '8', '9', 'E', 'F', 'G', 'H'}
PINS = {
    'manuscript': {'repository': 'https://github.com/elliotglazer/diophantine-z-q',
                   'commit': '97cec7fdd757d9a8e4f468151a47a6d3610fb2f2', 'file': 'diophantine_zq.pdf'},
    'fork': {'repository': 'https://github.com/Deicyde/diophantine-z-q',
             'commit': open(f'{HOME}/out/FORK_PIN').read().strip()},
    'nasqret': {'repository': 'https://github.com/nasqret/z-in-q-lean',
                'commit': open(f'{HOME}/out/NASQRET_PIN').read().strip(),
                'dependency': {'repository': 'https://github.com/elliotglazer/diophantine-z-q',
                               'commit': '2358394558aafae202a1ce6d3bd1b536b79ad3d0'}},
}


def slug(i):
    return re.sub(r'[^A-Za-z0-9._-]', '', i.replace(' ', '_'))


def load(path):
    if not os.path.exists(path):
        return {}
    return {i['id']: i for i in json.load(open(path))['items']}


def skeptics(iid, repo):
    out = []
    for n in (1, 2, 3, 4):
        p = f'{S}/skeptic/{slug(iid)}-{repo}-{n}.json'
        if os.path.exists(p):
            d = json.load(open(p))
            out.append({'n': n, 'refuted': bool(d.get('refuted')), 'reason': d.get('reason', ''),
                        **({'proposed': d['proposed']} if d.get('refuted') and d.get('proposed') else {})})
    return out


def main():
    items = json.load(open(f'{REPO}/data/items.json'))['items']
    by = {i['id']: i for i in items}
    batches = json.load(open(f'{REPO}/data/batches.json'))['batches']
    order = [i for b in batches for i in b['items']]
    batch_of = {i: b['id'] for b in batches for i in b['items']}
    cache = {}

    def files(b):
        if b not in cache:
            cmp_p = f'{S}/compare/{b}.json'
            cache[b] = (load(f'{S}/map/{b}.json'), load(f'{S}/verify/{b}.json'),
                        json.load(open(cmp_p)) if os.path.exists(cmp_p) else {},
                        load(f'{S}/judge/{b}.json'), load(f'{S}/judge/{b}-post.json'))
        return cache[b]

    out, counts = [], {}
    for iid in order:
        it = by[iid]
        b = batch_of[iid]
        m, v, c, j, jp = files(b)
        rec = {'id': iid, 'kind': it['kind'], 'section': it['section'], 'batch': b}
        for repo in REPOS:
            mv = (m.get(iid) or {}).get(repo)
            vv = (v.get(iid) or {}).get(repo)
            jv = (j.get(iid) or {}).get(repo)
            pv = (jp.get(iid) or {}).get(repo)
            cmp_ = c.get(f'{iid}|{repo}')
            ver = {'steps': []}
            if mv is not None:
                ver['steps'].append('mapper')
            if vv is not None:
                ver['steps'].append('verifier')
            verdict = None
            if mv is not None and vv is not None and cmp_ is not None:
                ver['mapper_verifier_agree'] = cmp_['agree']
                ver['keys_equal'] = cmp_.get('keys_equal', False)
                if cmp_['agree']:
                    verdict = mv
            elif mv is not None:
                verdict = mv
                ver['unverified'] = True
            if jv is not None:
                ver['steps'].append('judge')
                ver['judge'] = (j[iid].get('ruling') or {}).get(repo)
                verdict = jv
            if verdict is None:
                rec[repo] = {'judged': False, 'note': 'Not yet judged', 'verification': ver}
                counts['not judged'] = counts.get('not judged', 0) + 1
                continue
            claimed = verdict['status']
            sk = skeptics(iid, repo)
            need = 2 if claimed in FINDINGS else (1 if claimed == 'no-match' and it['section'] in FAR else 0)
            if pv is not None:
                ver['steps'].append('post-skeptic judge')
                ver['post_judge'] = (jp[iid].get('ruling') or {}).get(repo)
                verdict = pv
            for s in sk:
                ver['steps'].append(f"skeptic{s['n']}")
            if sk:
                ver['skeptics'] = sk
            if need:
                ver['claimed'] = claimed
                done = len(sk) >= need
                refuted = any(s['refuted'] for s in sk)
                kind = 'finding' if claimed in FINDINGS else 'absence'
                ver[kind] = 'pending' if not done and not refuted else ('unconfirmed' if refuted else 'confirmed')
                if pv is not None and pv['status'] != claimed:
                    # The post-skeptic judge changed the status: a new finding has had no skeptic
                    # of its own, so it is unconfirmed; any other status withdraws the claim.
                    ver[kind] = 'unconfirmed' if pv['status'] in FINDINGS else 'withdrawn'
                if pv is not None and pv['status'] == 'no-match' and kind == 'absence':
                    r2 = [s for s in sk if s['n'] == 3]
                    if r2:
                        ver[kind] = 'unconfirmed' if r2[0]['refuted'] else 'confirmed'
                        ver['second_round'] = True
                if pv is not None and pv['status'] in FINDINGS:
                    # A second round: skeptics 3 and 4 test the post-skeptic verdict afresh.
                    r2 = [s for s in sk if s['n'] in (3, 4)]
                    if len(r2) == 2:
                        ver[kind] = 'unconfirmed' if any(s['refuted'] for s in r2) else 'confirmed'
                        ver['second_round'] = True
            rec[repo] = dict(verdict, judged=True, verification=ver)
            counts[claimed] = counts.get(claimed, 0) + 1
        out.append(rec)
    # Orchestrator corrections (scratch/corrections.json): a note a later check showed inaccurate.
    cp = f'{S}/corrections.json'
    if os.path.exists(cp):
        byid = {r['id']: r for r in out}
        for c in json.load(open(cp))['items']:
            v = byid[c['id']][c['repo']]
            v['note'] = c['note']
            v['verification']['steps'].append('orchestrator correction')
            v['verification']['correction'] = c['source']
    doc = {'note': 'Verdicts of the mapping campaign: one per item and repository. See docs/taxonomy.md.',
           'pins': PINS, 'taxonomy': 'docs/taxonomy.md', 'items': out}
    json.dump(doc, open(f'{REPO}/data/mapping.json', 'w'), indent=1, ensure_ascii=False)
    print(len(out), 'items;', counts)


if __name__ == '__main__':
    main()
