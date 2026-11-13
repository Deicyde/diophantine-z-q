"""hoistopens.py FILE... : in generated helpers, move the `open` commands that directly follow a
`namespace X` line to just before it (as file-level opens in the Tau Ceti sources)."""
import sys,re
for f in sys.argv[1:]:
    L=open(f).read().split('\n'); out=[]; i=0; n=0
    while i<len(L):
        if L[i].startswith('namespace '):
            j=i+1
            while j<len(L) and L[j].strip()=='': j+=1
            opens=[]
            while j<len(L) and L[j].startswith('open ') and not L[j].rstrip().endswith(' in'):
                opens.append(L[j]); j+=1
            if opens:
                out+=opens+[L[i],'']; i=j; n+=1; continue
        out.append(L[i]); i+=1
    open(f,'w').write('\n'.join(out)); print(f,n)
