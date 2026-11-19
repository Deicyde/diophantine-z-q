#!/usr/bin/env python3
"""Render the skeptic prompts of batches from data/mapping.json (run merge.py first).

  render_skeptic.py <group> <batch>...   writes scratch/prompts/skeptic-<group>-{1,2}.txt for the
                                 claims of the batches that still lack that skeptic's file;
                                 prints the paths and claim counts

A finding (stronger, weaker, missing-hypothesis, differs, definition-differs) goes to skeptics 1
and 2. A no-match in Sections 7-9 or Appendices E-H goes to skeptic 1 only.
"""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from merge import FINDINGS, FAR, slug, HOME, S, REPO

m = json.load(open(f'{REPO}/data/mapping.json'))
t = open(f'{S}/prompts/skeptic.md').read()
group, bs = sys.argv[1], set(sys.argv[2:])
ROUND2 = group.startswith('r2')  # second round: findings a post-skeptic judge kept, skeptics 3 and 4
if True:
    for n in ((3, 4) if ROUND2 else (1, 2)):
        claims = []
        for r in m['items']:
            if r['batch'] not in bs:
                continue
            for repo in ('fork', 'nasqret'):
                v = r.get(repo) or {}
                if not v.get('judged'):
                    continue
                st = v['status']
                if ROUND2:
                    if not ('post_judge' in v.get('verification', {}) and st in FINDINGS):
                        continue
                elif not (st in FINDINGS or (n == 1 and st == 'no-match' and r['section'] in FAR)):
                    continue
                out = f'{S}/skeptic/{slug(r["id"])}-{repo}-{n}.json'
                if os.path.exists(out):
                    continue
                decls = ', '.join(f"{l['decl']} ({l.get('repo', repo)}, {l['role']}, {l['standing']})"
                                  for l in v.get('lean', [])) or 'none'
                extra = f"\n  searched before: {'; '.join(v.get('searched', []))[:600]}" if st == 'no-match' else ''
                claims.append(f'- item "{r["id"]}", repository {repo}: claim `{st}`.\n  note: {v["note"]}\n'
                              f'  declarations: {decls}{extra}\n  write: {out}')
        if not claims:
            continue
        p = f'{S}/prompts/skeptic-{group}-{n}.txt'
        open(p, 'w').write(t.replace('{N}', str(n)).replace('{CLAIMS}', '\n'.join(claims)).replace('W/', f'{HOME}/'))
        print(p, len(claims))
