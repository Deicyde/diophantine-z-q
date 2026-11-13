import sys,os,re
sys.path.insert(0,os.path.dirname(__file__))
from decls import decls,p
H=os.path.expanduser('~')
O=H+'/tc-oct16'; N=H+'/tc-nov01'
allm=[l.strip() for l in open(H+'/dzq-runs/tc/kw-all.txt') if l.strip()]
new=[l.strip() for l in open(H+'/dzq-runs/tc/kw-new-nov01.txt') if l.strip()]
shared=[m for m in allm if m not in new]
oct_def={}; added={}  # name -> module
for m in shared:
    o=set(decls(p(O,m))); n=set(decls(p(N,m)))
    for x in o: oct_def[x]=m
    for x in n-o: added[x]=m
# also decls anywhere in oct16 closure-wide? use oct16-all
print('added in shared modules:',len(added))
newdefs={}
for m in new:
    for x in decls(p(N,m)): newdefs[x]=m
clash=[(x,newdefs[x],oct_def[x]) for x in newdefs if x in oct_def]
print('CLASHES new-module decl already in oct16 shared module:',len(clash))
for c in sorted(clash,key=lambda c:c[1]): print('  ',*c)
# usage of added decls in new modules: match last component(s)
print('USES of decls added after oct16:')
uses={}
for m in new:
    txt=open(p(N,m),encoding='utf-8').read()
    for x,src in added.items():
        parts=x.split('.')
        cands={x,'.'.join(parts[-2:]),parts[-1]}
        for c in cands:
            if len(c)<4: continue
            if re.search(r'(?<![\w.])'+re.escape(c)+r'(?![\w\'])',txt):
                uses.setdefault(m,set()).add((x,src)); break
for m in sorted(uses):
    print(m)
    for x,src in sorted(uses[m]): print('    ',x,'  <-',src)
