"""Eliminate outputs, reducing substitutions modulo retained quadratic rows.

Every reduction records a polynomial multiple of an unaffected original row.
Those rows remain in the system, so the operation is reversible on their zeros.
"""
from search import *
import time
import random
ORDER=0
RANK={}
SOURCE=BASE/'compiler/translated/compiled-ir.json'

def lead(p):
    return max(p,key=lambda k:(len(k[1]),tuple(sorted(RANK.get(v,v) for v in k[1])),k[0])) if p else None

def divide(a,b):
    s,m=a;t,n=b
    if s<t:return None
    rem=list(m)
    for x in n:
        if x not in rem:return None
        rem.remove(x)
    return s-t,tuple(rem)

def basis_for(excluded):
    basis={}
    for rid,p0 in c.rows.items():
        if rid in excluded:continue
        p=p0.copy();combo={rid:{(0,()):F(1)}}
        while p and C.degree(p)==2:
            if len(p)>100 or len(combo)>30:break
            k=lead(p)
            if k not in basis:
                f=p[k];p={a:b/f for a,b in p.items()}
                combo={r:{a:b/f for a,b in q.items()} for r,q in combo.items()}
                basis[k]=(p,combo);break
            q,qc=basis[k];f=-p[k]
            p=C.add(p,q,f)
            for r,q in qc.items():combo[r]=C.add(combo.get(r,{}),q,f)
    return basis

def reduce_high(p,basis):
    trace={}; steps=0
    while C.degree(p)>2:
        if len(p)>1200 or steps>500:return None
        k=lead(p);found=False
        # At most six degree-two divisors exist for a coordinate quartic.
        mm=k[1]
        for i in range(len(mm)):
            for j in range(i+1,len(mm)):
                d=(0,(mm[i],mm[j]))
                if d not in basis:continue
                rem=divide(k,d)
                q,qc=basis[d];factor={rem:-p[k]}
                p=C.add(p,C.multiply(q,factor));steps+=1
                for r,q in qc.items():trace[r]=C.add(trace.get(r,{}),C.multiply(q,factor))
                found=True;break
            if found:break
        if not found:return None
    return p,trace

def run(max_orders=1,prior=None):
    global ORDER,RANK
    start=time.time();ops=list(prior['operations']) if prior else [];scanned=0;order=0
    while order<max_orders:
        ORDER=order
        ids=sorted(c.coordinates)
        if order==0:RANK={v:v for v in ids}
        elif order==1:RANK={v:-v for v in ids}
        else:
            shuffled=ids.copy();random.Random(order).shuffle(shuffled)
            RANK=dict(zip(ids,shuffled))
        found=False
        for v in sorted(c.coordinates,reverse=True):
            if v in c.protected:continue
            affected=c.incidence[v]
            pivots=[(r,c.pivot_replacement(v,r)) for r in affected]
            pivots=[(r,p) for r,p in pivots if p and C.degree(p[1])==2]
            if not pivots:continue
            basis=basis_for(affected)
            for rid,(a,replacement) in pivots:
                scanned+=1;changes={};traces={}
                for other in sorted(affected-{rid}):
                    sub=C.substitute(c.rows[other],v,replacement)
                    out=reduce_high(sub,basis)
                    if out is None:break
                    changes[other],traces[other]=out
                else:
                    op={'coordinate':v,'name':c.coordinates[v]['name'],'pivot':rid,
                        'replacement':C.terms(replacement),
                        'changes':[{'row':r,'result':C.terms(p),'multiples':[{'row':s,'factor':C.terms(q)} for s,q in traces[r].items() if q]} for r,p in changes.items()]}
                    ops.append(op)
                    for r,p in changes.items():c.replace_row(r,p)
                    c.replace_row(rid,{})
                    del c.rows[rid];del c.coordinates[v];c.incidence.pop(v,None)
                    print('ELIMINATED',v,op['name'],len(c.coordinates),flush=True)
                    found=True;break
            if found:break
        if not found:
            print('ORDER COMPLETE',order,flush=True);order+=1
    result={'baselineSha256':C.digest(SOURCE),'operations':ops,
      'counts':{'coordinates':len(c.coordinates),'residuals':len(c.rows),'degree':max(map(C.degree,c.rows.values()))},
      'scanned':scanned,'elapsedSeconds':time.time()-start}
    (OUT/'modulo-certificate.json').write_text(json.dumps(result,indent=2)+'\n')
    (OUT/'candidate-ir.json').write_text(json.dumps(c.output(),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='operations'},indent=2),flush=True)

if __name__=='__main__':run()
