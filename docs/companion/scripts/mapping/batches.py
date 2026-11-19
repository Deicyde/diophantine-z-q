#!/usr/bin/env python3
"""Split the items into mapping batches of about 12, in document order.

An item and everything inside it (its enclosing chain, followed to the top) form one group, and
a group is never split. Batches do not cross a section, except that Sections 1 and 4 form one
batch (the pilot's). A section is cut into ceil(n/12) batches of nearly equal size at group
boundaries.
"""
import json, math, os
HOME = os.environ.get('ZQ_WORK') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
REPO = f'{HOME}/repo'
TARGET = 12

items = json.load(open(f'{REPO}/data/items.json'))['items']
by = {it['id']: it for it in items}
start = lambda it: (min(a for a, b in it['lines']), -max(b for a, b in it['lines']))
items.sort(key=start)
pos = {it['id']: k for k, it in enumerate(items)}


def root(i):
    while by[i].get('enclosing'):
        i = by[i]['enclosing']
    return i


groups = {}
for it in items:
    groups.setdefault(root(it['id']), []).append(it['id'])
ordered = sorted(groups.values(), key=lambda g: min(pos[i] for i in g))
for g in ordered:
    g.sort(key=lambda i: pos[i])

by_section = {}
for g in ordered:
    sec = by[g[0]]['section']
    by_section.setdefault('1+4' if sec in ('1', '4') else sec, []).append(g)

batches = []
for sec, gs in by_section.items():
    n = sum(len(g) for g in gs)
    k = max(1, math.ceil(n / TARGET)) if sec != '1+4' else 1
    size = n / k
    cur, acc, part = [], 0, 1
    for g in gs:
        if cur and acc + len(g) / 2 > size * part and part < k:
            batches.append((sec, part, cur))
            cur, part = [], part + 1
        cur += g
        acc += len(g)
    batches.append((sec, part, cur))


# A batch of fewer than 6 items joins its neighbour in document order while the two stay at 13 or
# fewer, even across a section.
merged = []
for b in batches:
    if merged and (len(b[2]) < 6 or len(merged[-1][2]) < 6) and len(merged[-1][2]) + len(b[2]) <= 13:
        sec, p, ids = merged[-1]
        merged[-1] = (sec if sec == b[0] else f'{sec}/{b[0]}', p, ids + b[2])
    else:
        merged.append(b)
batches, seen = [], {}
for sec, p, ids in merged:
    seen[sec] = seen.get(sec, 0) + 1
    batches.append((sec, seen[sec], ids))


def bid(sec, p):
    if '/' in sec:
        return '+'.join(bid(s, p).rsplit('-', 1)[0] for s in sec.split('/')) + f'-{p}'

    s = 'S01+S04' if sec == '1+4' else (f'S{int(sec):02d}' if sec.isdigit() else ('Refs' if sec == 'References' else f'App{sec}'))
    return f'{s}-{p}'


out = {'note': 'mapping batches, in document order; an item is kept with the items inside it',
       'batches': [{'id': bid(sec, p), 'section': sec, 'items': ids} for sec, p, ids in batches]}
json.dump(out, open(f'{REPO}/data/batches.json', 'w'), indent=1, ensure_ascii=False)
print(len(batches), 'batches;', ' '.join(f"{b['id']}:{len(b['items'])}" for b in out['batches']))
