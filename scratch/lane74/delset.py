import json,sys
g=json.load(open('/home/jackmccarthy/lane74-tools/g0.json'))
imp=g['imp']; mods=set(imp)
H=set(json.load(open('/home/jackmccarthy/lane74-tools/H.json')))
def under(p): return {m for m in mods if m==p or m.startswith(p+'.')}
D=set()
D|=under('ZInQKernel.RouteK'); D.discard('ZInQKernel.RouteK.Selmer.CharSum')
for p in ['TYZChain','TYZDecomp','TYZGenus','GZDecomp','GZStatements','GZTheta','HeckeFE']:
    D|=under('ZInQKernel.Contrib.'+p)
D|={'ZInQKernel.MainLiterature','ZInQKernel.Hypotheses.CertifiedRank','ZInQKernel.Hypotheses.CR3Literature','ZInQKernel.Hypotheses.TYZInputs','ZInQKernel.OneProof.TYZSplit','ZInQKernel.OneProof.TopChain'}
# Contrib/OneProof CR3 roots: OneProof.Main imports other than H
roots=[i for i in imp['ZInQKernel.OneProof.Main'] if i not in H]
def clos(rs):
    seen=set(); st=list(rs)
    while st:
        m=st.pop()
        if m in seen: continue
        seen.add(m); st+=imp.get(m,[])
    return seen
C=clos(roots)
cop={m for m in C if m.startswith('ZInQKernel.Contrib.OneProof') and m not in H}
named=set(D)
D|=cop
print('Contrib.OneProof in CR3 closure (not H):',len(cop))
extra=set(sys.argv[1:])
D|=extra
protect=lambda m: m in H or m.startswith('ZInQKernel.OneProof.H.') or m.startswith('ZInQKernel.HDecomp') or m in ('ZInQKernel','ZInQKernel.Main','ZInQKernel.MainGreenTao','ZInQKernel.OneProof.Main','ZInQKernel.Contrib.AllContrib')
findings={}
changed=True
forced=set()
while changed:
    changed=False
    for m in mods-D:
        bad=[i for i in imp[m] if i in D]
        if bad:
            if protect(m): findings[m]=bad
            else: D.add(m); forced.add(m); changed=True
print('total D',len(D))
print('forced (beyond named + cop):')
for m in sorted(forced): print('  ',m, [i for i in imp[m] if i in D][:3])
print('protected importers:')
for m,b in sorted(findings.items()): print('  ',m,b[:6], len(b))
json.dump(sorted(D),open('/home/jackmccarthy/lane74-tools/D.json','w'))
print('cop list:'); 
for m in sorted(cop): print('  ',m)
