#!/usr/bin/env python3
"""Mark in the dependency's index the Props that nasqret's headline theorems assume through it.

Usage: python3 -I mark_dependency.py <raw dependency index> <nasqret index> <out json>
"""
import json
import sys

raw, nas, out = sys.argv[1:4]
idx = json.load(open(raw, encoding='utf-8'))
used = json.load(open(nas, encoding='utf-8'))['assumed_in_dependency']
for r in idx['declarations']:
    if r['name'] in used and r['prop']:
        r['standing'] = 'assumed'
        r['assumed_by'] = used[r['name']]
counts = {}
for r in idx['declarations']:
    counts[r['standing']] = counts.get(r['standing'], 0) + 1
idx['standing_counts'] = counts
idx['note'] = 'indexed for lookups; assumed marks are those of nasqret/z-in-q-lean headline theorems'
json.dump(idx, open(out, 'w', encoding='utf-8'), ensure_ascii=False)
print(json.dumps(counts))
