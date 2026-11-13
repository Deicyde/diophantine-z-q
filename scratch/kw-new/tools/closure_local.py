import os,re,sys
root='ZInQKernel/Contrib/TauCeti'
def p(m): return m.replace('.','/')+'.lean'
def deps(m):
    f=p(m)
    if not os.path.exists(f): return None
    return re.findall(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(ZInQKernel\.Contrib\.TauCeti\.\S+)',open(f).read(),re.M)
S=set(); st=[sys.argv[1]]; missing=set()
while st:
    x=st.pop()
    if x in S: continue
    S.add(x); d=deps(x)
    if d is None: missing.add(x); continue
    st.extend(d)
print(len(S),'modules; missing',sorted(missing))
if len(sys.argv)>2: open(sys.argv[2],'w').write('\n'.join(sorted(S))+'\n')
