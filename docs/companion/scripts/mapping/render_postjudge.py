#!/usr/bin/env python3
"""Render the post-skeptic judge prompt for every refuted claim without a post-judge verdict.

  render_postjudge.py <group>    writes scratch/prompts/postjudge-<group>.txt; prints its path
"""
import json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from merge import slug, HOME, S, REPO

m = json.load(open(f'{REPO}/data/mapping.json'))
claims = []
for r in m['items']:
    pp = f"{S}/judge/{r['batch']}-post.json"
    done = {i['id']: i for i in json.load(open(pp))['items']} if os.path.exists(pp) else {}
    for repo in ('fork', 'nasqret'):
        v = r.get(repo) or {}
        sk = v.get('verification', {}).get('skeptics', [])
        if not any(s['refuted'] for s in sk) or repo in (done.get(r['id']) or {}):
            continue
        files = ', '.join(f"{S}/skeptic/{slug(r['id'])}-{repo}-{s['n']}.json" for s in sk)
        claims.append(f'- item "{r["id"]}", repository {repo}, batch {r["batch"]}: claim `{v["verification"]["claimed"]}`; skeptics: {files}')
if not claims:
    print('NONE'); sys.exit(0)
p = f'{S}/prompts/postjudge-{sys.argv[1]}.txt'
t = open(f'{S}/prompts/postjudge.md').read().replace('{CLAIMS}', '\n'.join(claims)).replace('W/', f'{HOME}/')
open(p, 'w').write(t)
print(p, len(claims))
