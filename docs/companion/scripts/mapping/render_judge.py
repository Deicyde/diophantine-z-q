#!/usr/bin/env python3
"""Render the judge prompt of a batch from scratch/compare/<batch>.json; print its path or NONE."""
import json, os, sys
HOME = os.environ.get('ZQ_WORK') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
S = f'{HOME}/scratch'
b = sys.argv[1]
c = json.load(open(f'{S}/compare/{b}.json'))
items = '\n'.join(f'- {k.replace("|", " | ")}: {r["why"]}' for k, r in c.items() if not r['agree'])
if not items:
    print('NONE'); sys.exit(0)
t = open(f'{S}/prompts/judge.md').read().replace('{BATCH}', b).replace('{ITEMS}', items).replace('W/', f'{HOME}/')
open(f'{S}/prompts/judge-{b}.txt', 'w').write(t)
print(f'{S}/prompts/judge-{b}.txt')
