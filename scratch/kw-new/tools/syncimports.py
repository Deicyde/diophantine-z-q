"""syncimports.py HELPER... : add to each Backport helper the imports of its nov01 source module
(rewritten to ZInQKernel.Contrib.TauCeti), plus the Backport helpers of those imports."""
import sys,os,re
H=os.path.expanduser('~')
def helper_of(mod):  # ZInQKernel.Contrib.TauCeti.X -> backport helper module if exists
    p='ZInQKernel/Contrib/TauCeti/Backport/'+mod[len('ZInQKernel.Contrib.TauCeti.'):].replace('.','/')+'.lean'
    return 'ZInQKernel.Contrib.TauCeti.Backport.'+mod[len('ZInQKernel.Contrib.TauCeti.'):] if os.path.exists(p) else None
for f in sys.argv[1:]:
    rel=f[len('ZInQKernel/Contrib/TauCeti/Backport/'):-5]
    src=H+'/tc-nov01/TauCeti/'+rel+'.lean'
    s=open(f).read()
    have=set(re.findall(r'^(?:public\s+)?import\s+(?:all\s+)?(\S+)',s,re.M))
    me='ZInQKernel.Contrib.TauCeti.Backport.'+rel.replace('/','.')
    new=[]
    for pub,m in re.findall(r'^(public\s+)?import\s+(\S+)',open(src).read(),re.M):
        if m.startswith('TauCeti.'): m='ZInQKernel.Contrib.'+m
        if m.startswith('ZInQKernel') and not os.path.exists(m.replace('.','/')+'.lean'):
            print('  MISSING',m); continue
        cands=[m]
        if m.startswith('ZInQKernel'):
            h=helper_of(m)
            if h and h!=me: cands.append(h)
        for c in cands:
            if c not in have: new.append(('public ' if pub else '')+'import '+c); have.add(c)
    if new:
        last=list(re.finditer(r'^(?:public\s+)?import\s+.*$',s,re.M))[-1]
        s=s[:last.end()]+'\n'+'\n'.join(new)+s[last.end():]
        open(f,'w').write(s)
    print(f,'+',len(new))
