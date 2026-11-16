"""Load the EnvDump facts (external, built modules) into Python structures."""
import json, pickle, os
DUMP = '/home/jackmccarthy/cloud-b3/w13/normalize/work/dump_all.jsonl'
CACHE = '/home/jackmccarthy/cloud-b3/w13/normalize/work/envdb.pickle'
class ExtDB:
    pass
def load():
    if os.path.exists(CACHE) and os.path.getmtime(CACHE) > os.path.getmtime(DUMP):
        return pickle.load(open(CACHE, 'rb'))
    db = ExtDB()
    db.mods = {}      # name -> dict(imports, ns, consts, prot, inst, simp, alias)
    for line in open(DUMP):
        d = json.loads(line)
        if 'extnames' in d:
            continue
        m = d['m']
        db.mods[m] = {
            'imports': d['imports'],
            'ns': d['ns'],
            'consts': [c for c, p in d['consts']],
            'prot': [c for c, p in d['consts'] if p],
            'inst': [(n, s) for n, s in d['inst']],
            'simp': [(n, s, k) for n, s, k in d['simp']],
            'alias': [(a, t) for a, t in d['alias']],
        }
    pickle.dump(db, open(CACHE, 'wb'))
    return db
def closure(db, roots):
    seen = set(); st = list(roots)
    while st:
        m = st.pop()
        if m in seen or m not in db.mods: continue
        seen.add(m); st.extend(db.mods[m]['imports'])
    return seen
