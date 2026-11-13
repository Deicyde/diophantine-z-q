"""addhelpers.py FILE... : for each import of a module that has a Backport helper, add the helper
import right after it (same visibility). Imports of modules REPLACED by a full nov01 Backport copy
(listed in REPLACED) are redirected to the copy."""
import sys,os,re
REPLACED={'ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.PrescribedInvariant'}
def helper(m):
    rel=m[len('ZInQKernel.Contrib.TauCeti.'):]
    p='ZInQKernel/Contrib/TauCeti/Backport/'+rel.replace('.','/')+'.lean'
    return 'ZInQKernel.Contrib.TauCeti.Backport.'+rel if os.path.exists(p) else None
for f in sys.argv[1:]:
    s=open(f).read(); me=f[:-5].replace('/','.')
    have=set(re.findall(r'^(?:public\s+)?import\s+(?:all\s+)?(\S+)',s,re.M))
    out=[]; n=0
    for line in s.split('\n'):
        m=re.match(r'^((?:public\s+)?import\s+)(ZInQKernel\.Contrib\.TauCeti\.(?!Backport)\S+)\s*$',line)
        if m and m.group(2) in REPLACED and not me.startswith('ZInQKernel.Contrib.TauCeti.Backport'):
            out.append(m.group(1)+helper(m.group(2))); n+=1; continue
        out.append(line)
        if m:
            h=helper(m.group(2))
            if h and h!=me and h not in have and m.group(2) not in REPLACED:
                out.append(m.group(1)+h); have.add(h); n+=1
    if n: open(f,'w').write('\n'.join(out))
    if n: print(f,'+',n)
