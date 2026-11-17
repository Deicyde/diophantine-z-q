import json,collections,sys
d=json.load(open(sys.argv[1]))
nm={c['id']:c['name'] for c in d['coordinates']}
rows=d['residuals']
# definitions: rows named '<coord>.definition' with linear term in coord
defs={}
for r in rows:
    if r['name'].endswith('.definition') or '.definition.' in r['name']:
        pass
rname={r["id"]:r["name"] for r in rows}
byname={c['name']:c['id'] for c in d['coordinates']}
occ=collections.defaultdict(list)
for r in rows:
    for t in r['terms']:
        for v in set(t['monomial']): occ[v].append((r['id'],t['monomial']))
for c in d['coordinates']:
    if not c['name'].endswith('.quadratic'): continue
    if c['block'] in ('base',) : continue
    base=c['name'][:-len('.quadratic')]
    dr=[r for r in rows if r['name']==base+'.definition']
    if not dr: continue
    dr=dr[0]
    # definition degree of the expression (excluding v)
    expr=[t for t in dr['terms'] if t['monomial']!=[c['id']]]
    edeg=max(len(t['monomial']) for t in expr)
    bad=collections.Counter()
    for rid,m in occ[c['id']]:
        if rid==dr['id']: continue
        k=len(m)  # degree of monomial
        if k==1: newdeg=edeg
        else:
            other=[x for x in m if x!=c['id']]
            newdeg=edeg*(2 if not other else 1)+ (len(other))
        if newdeg>2: bad[rname[rid]]+=1
    print(f"{c['name']:50s} {c['block'][:18]:18s} exprdeg={edeg} badrows={len(bad)} {list(bad)[:4]}")
