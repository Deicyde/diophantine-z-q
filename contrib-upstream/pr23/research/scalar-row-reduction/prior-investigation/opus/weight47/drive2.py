import subprocess, sys
from concurrent.futures import ThreadPoolExecutor
base={'d':(0,0,1),'d2':(0,0,2),'d3':(0,0,3),'q1':(0,1,-1),'q1^2':(0,2,-2),'q1^3':(0,3,-3),'q1^4':(0,4,-4),'E':(0,1,1)}
MODELS={'r0':dict(base,F=(0,-1,5)),'r0noF':dict(base),
        'rA':dict(base,F=(10,-1,5),C=(1,0,0),A=(2,0,0),Ad=(2,0,1),A2d2=(4,0,2),A4d4=(8,0,4))}
X=[(0,0,k) for k in range(9)]
def one(job):
    model,N,budget,freeA=job; S0=MODELS[model]
    inp=f"{len(S0)}\n"+"\n".join(' '.join(map(str,v)) for v in S0.values())+f"\n{len(X)}\n"+"\n".join(' '.join(map(str,v)) for v in X)+f"\n{N} {budget} {freeA}\n"
    return job, subprocess.run(['./search2'],input=inp,capture_output=True,text=True).stdout
if __name__=='__main__':
    jobs=[(a.split(':')[0],*map(int,a.split(':')[1:])) for a in sys.argv[1:]]
    with ThreadPoolExecutor(min(20,len(jobs))) as ex:
        for j,o in ex.map(one,jobs): print(j[0],o.strip(),flush=True)
