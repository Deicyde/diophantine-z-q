#!/usr/bin/env python3
"""Render the mapper or verifier prompt of a batch: render.py <mapper|verifier> <batch>."""
import os, sys
HOME = os.environ.get('ZQ_WORK') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
role, b = sys.argv[1], sys.argv[2]
out = f"{HOME}/scratch/{'map' if role == 'mapper' else 'verify'}/{b}.json"
other = 'verify' if role == 'mapper' else 'map'
t = open(f'{HOME}/scratch/prompts/mapper.md').read()
t = t.replace('{ROLE}', role).replace('{BATCH}', b).replace('{OUT}', out).replace('W/', f'{HOME}/')
t += (f'\nWork independently: do not read {HOME}/scratch/{other}/, {HOME}/scratch/judge/, {HOME}/scratch/skeptic/ '
      f'or other agents\' directories under {HOME}/scratch/agents/.\n')
print(t)
