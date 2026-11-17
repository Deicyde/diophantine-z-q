"""Expose and remove common-radical directions by invertible linear shears."""
from search import *
import time

def kernel(c):
    equations=[]
    for p in c.rows.values():
        deriv={}
        for (s,m),a in p.items():
            if len(m)!=2:continue
            assert s==0
            i,j=m
            deriv.setdefault(i,{})[j]=deriv.setdefault(i,{}).get(j,F(0))+a
            deriv.setdefault(j,{})[i]=deriv.setdefault(j,{}).get(i,F(0))+a
        equations.extend(deriv.values())
    # Protected coordinates must not change under the direction.
    equations.extend({i:F(1)} for i in c.protected if i in c.coordinates)
    equations.sort(key=len);basis={}
    for q0 in equations:
        q=q0.copy()
        while q:
            j=min(q);a=q[j]
            if j not in basis:
                basis[j]={k:v/a for k,v in q.items()};break
            for k,v in basis[j].items():
                q[k]=q.get(k,F(0))-a*v
                if not q[k]:del q[k]
    vectors=[]
    for free in sorted(set(c.coordinates)-set(basis)):
        vec={free:F(1)}
        for j,q in sorted(basis.items(),reverse=True):
            val=-sum(a*vec.get(k,F(0)) for k,a in q.items() if k!=j)
            if val:vec[j]=val
        vectors.append((free,vec))
    return vectors

def run():
    start=time.time()
    cert=json.loads((OUT/'modulo-certificate.json').read_text())
    c=C.Compiler(json.loads((OUT/'candidate-ir.json').read_text()))
    ops=cert['operations'];rounds=[]
    while True:
        directions=kernel(c)
        rounds.append(len(directions));print('KERNEL',len(directions),flush=True)
        if not directions:break
        for free,vec in directions:
            shears=[]
            for v,a in vec.items():
                if v==free:continue
                assert v not in c.protected
                q={(0,(v,)):F(1),(0,(free,)):a}
                for rid in list(c.incidence[v]):c.replace_row(rid,C.substitute(c.rows[rid],v,q))
                shears.append({'coordinate':v,'factor':str(a)})
            ops.append({'kind':'shear','free':free,'shears':shears})
            assert not any(free in m and len(m)>1 for p in c.rows.values() for s,m in p)
            pivots=[]
            for rid in c.incidence[free]:
                result=c.elimination(free,rid)
                if result:pivots.append((len(result[1]),rid,result))
            if not pivots:raise RuntimeError('Free coordinate has no pivot')
            _,rid,(a,q,affected,changes)=min(pivots)
            ops.append({'coordinate':free,'name':c.coordinates[free]['name'],'pivot':rid,
                        'replacement':C.terms(q),'changes':[{'row':r,'result':C.terms(p),'multiples':[]} for r,p in changes.items()]})
            assert c.eliminate(free,rid)
            print('ELIMINATE',free,len(c.coordinates),flush=True)
    cert.update({'operations':ops,'counts':{'coordinates':len(c.coordinates),'residuals':len(c.rows),'degree':max(map(C.degree,c.rows.values()))},
                 'affineRounds':rounds,'affineElapsedSeconds':time.time()-start})
    (OUT/'modulo-certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
    (OUT/'candidate-ir.json').write_text(json.dumps(c.output(),indent=2)+'\n')
    print(cert['counts'],flush=True)

if __name__=='__main__':run()
