"""usehelpers.py FILE... : add `import H` for every Backport helper H (other than FILE itself)
one of whose declarations is mentioned in FILE."""
import sys,os,re,glob
sys.path.insert(0,os.path.dirname(__file__))
from decls import decls
helpers={}
for h in glob.glob('ZInQKernel/Contrib/TauCeti/Backport/**/*.lean',recursive=True):
    names=set()
    for d in decls(h):
        parts=d.split('.')
        names.add(parts[-1])
    # to_additive names
    txt=open(h).read()
    names|=set(re.findall(r'@\[to_additive\s+([A-Za-z_][\w\']*)',txt))
    helpers[h[:-5].replace('/','.')]={n for n in names if len(n)>=5}
for f in sys.argv[1:]:
    s=open(f).read(); me=f[:-5].replace('/','.')
    body=re.sub(r'^(?:public\s+)?import .*$','',s,flags=re.M)
    toks=set(t.split('.')[-1] for t in re.findall(r"[A-Za-z_][\w.']*",body))
    add=[]
    for h,names in helpers.items():
        if h==me or ('import '+h) in s: continue
        if 'Global.PrescribedInvariant' in h and 'Backport' in me: pass
        hit=names & toks
        if hit: add.append((h,sorted(hit)[:3]))
    if add:
        last=list(re.finditer(r'^(?:public\s+)?import\s+.*$',s,re.M))[-1]
        s=s[:last.end()]+'\n'+'\n'.join('import '+h for h,_ in add)+s[last.end():]
        open(f,'w').write(s)
        for h,hit in add: print(f.split('TauCeti/')[-1],'<-',h.split('Backport.')[-1],hit)
