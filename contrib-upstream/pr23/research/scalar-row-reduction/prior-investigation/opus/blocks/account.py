import json,sys,collections,re
B=sys.argv[1]
raw=json.load(open(B+'/raw-translated-ir.json'))
cert=json.load(open(B+'/compiled/reduction-certificate.json'))
cand=json.load(open(B+'/candidate-ir.json'))
fin=json.load(open(B+'/final/integer-candidate-ir.json'))
elim={o['coordinate'] for o in cert['operations'] if o['kind']=='eliminate'}
cn={c['name'] for c in cand['coordinates']}; fn={c['name'] for c in fin['coordinates']}
print('transport-removed:',cn-fn, 'added', fn-cn)
print('eliminated:',[raw['coordinates'][i]['name'] for i in sorted(elim)])
per=collections.defaultdict(lambda:[0,0,0])
for c in raw['coordinates']:
    per[c['block']][0]+=1
    if c['name'] in fn: per[c['block']][1]+=1
tot=0
for b,v in per.items(): print(f"{b:50s} raw {v[0]:3d} final {v[1]:3d}"); tot+=v[1]
print('total final',tot,len(fin['coordinates']))
if len(sys.argv)>2:
  for c in raw['coordinates']:
    if c['block']==sys.argv[2]: print(c['id'],c['name'], 'FINAL' if c['name'] in fn else 'gone')
