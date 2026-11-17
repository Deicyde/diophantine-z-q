import json,collections,sys
d=json.load(open(sys.argv[1]))
occ=collections.defaultdict(list)
for r in d['residuals']:
    for t in r['terms']:
        m=t['monomial']
        for v in set(m):
            other=[names for names in m if names!=v]
            occ[v].append((r['name'], 'lin' if len(m)==1 else ('sq' if m[0]==m[1] else 'x'+str(other[0]))))
nm={c['id']:c['name'] for c in d['coordinates']}
for c in d['coordinates']:
    if sys.argv[2] not in c['name']: continue
    o=occ[c['id']]
    rows=collections.defaultdict(list)
    for r,k in o: rows[r].append(k if not k.startswith('x') else nm[int(k[1:])])
    print(c['name'], 'rows',len(rows)); 
    for r,k in rows.items(): print('    ',r, k[:8])
