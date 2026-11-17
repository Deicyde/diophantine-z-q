"""cm-branch2: generate ZInQKernel/Contrib/OneProof/CMBranch/Top2.lean (the hand-fold dry run on the current top).
Walks the chain from TOP down to sixContactMin_of_open4_hf_pz_eb, copies each one-step theorem verbatim with
(c : CMBranch.CMInputs2) threaded and the callee renamed to `<callee>_cm2 (c := c)` (as cm-branch's mk_top.py)."""
import re,glob,sys
TOP=sys.argv[1] if len(sys.argv)>1 else 'sixContactMin_of_open72'
src={f:open(f).read() for f in glob.glob('ZInQKernel/OneProof/H/*.lean')}
def get(name):
    for f,s in src.items():
        m=re.search(r'^theorem '+re.escape(name)+r'(?=[\s(])', s, re.M)
        if m:
            lines=s[m.start():].split('\n'); out=[lines[0]]
            for l in lines[1:]:
                if l and not l.startswith(' '): break
                out.append(l)
            return '\n'.join(out).rstrip()
    raise Exception(name)
chain=[]
cur=TOP
while cur!='sixContactMin_of_open4_hf_pz_eb':
    t=get(cur)
    body=t.split(':=',1)[1]
    calls=[c for c in re.findall(r"(sixContactMin_of_[A-Za-z0-9_']+)",body) if c!=cur]
    chain.append((cur,t,calls[0])); cur=calls[0]
out=[]
for name,t,callee in reversed(chain):
    i=t.index('ZInQ.SixContactMin :=')
    j=t.rindex(':',0,i)
    sig=t[:j].rstrip()+' (c : CMBranch.CMInputs2) '+t[j:i]+'ZInQ.SixContactMin :='
    sig=sig.replace('theorem '+name,'theorem '+name+'_cm2',1)
    body=t[i+len('ZInQ.SixContactMin :='):]
    assert body.count(callee)==1,(name,callee)
    body=body.replace(callee,callee+'_cm2 (c := c)')
    out.append(f'/-- `{name}` with the base switched to `sixContactMin_of_open4_hf_pz_eb_cm2` (cm-branch2). -/\n'+sig+body)
hdr=open('scratch/cm-branch2/gen/top2_header.lean').read()
ftr='''
end HSyn
end
end HDec
'''
open('ZInQKernel/Contrib/OneProof/CMBranch/Top2.lean','w').write(hdr+'\n\n'.join(out)+'\n'+ftr)
print(len(chain), [c[0] for c in chain][:4])
