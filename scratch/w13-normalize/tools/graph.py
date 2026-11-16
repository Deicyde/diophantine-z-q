import os,re,json,sys
ROOT='/home/jackmccarthy/cloud-b3/w13/normalize/repo'
def staged_files():
    out=[]
    for d in ['ZInQKernel/Contrib/CloudB3W13','ZInQKernel/Contrib/CloudB3W13Shared']:
        for dp,dn,fn in os.walk(os.path.join(ROOT,d)):
            for f in fn:
                if f.endswith('.lean'):
                    out.append(os.path.relpath(os.path.join(dp,f),ROOT))
    return sorted(out)
def mod_of(path): return path[:-5].replace('/','.')
def path_of(mod): return mod.replace('.','/')+'.lean'
IMP=re.compile(r'^import\s+(\S+)',re.M)
def imports(path):
    s=open(os.path.join(ROOT,path),encoding='utf-8').read()
    return IMP.findall(s)
def graph():
    fs=staged_files()
    g={mod_of(f):imports(f) for f in fs}
    return g
def closure(g,roots):
    seen=set();st=list(roots)
    while st:
        m=st.pop()
        if m in seen or m not in g: continue
        seen.add(m)
        st.extend(g[m])
    return seen
if __name__=='__main__':
    g=graph()
    roots=sys.argv[1:]
    c=closure(g,roots)
    ext=set()
    for m in c:
        for i in g[m]:
            if i not in g: ext.add(i)
    print(len(c),'staged modules in cone;',len(ext),'external imports')
    tot=sum(os.path.getsize(os.path.join(ROOT,path_of(m))) for m in c)
    print('bytes',tot)
    json.dump(sorted(c),open('/home/jackmccarthy/cloud-b3/w13/normalize/work/cone.json','w'),indent=0)
