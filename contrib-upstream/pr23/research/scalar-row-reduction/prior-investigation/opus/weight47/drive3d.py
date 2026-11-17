# r>0 detectors: lattice (2*ord_A, ord_e, ord_delta); A = C^2 with C stored (heightProduct x or affine sum).
import subprocess, sys
from concurrent.futures import ThreadPoolExecutor
S0={'d':(0,0,1),'d2':(0,0,2),'d3':(0,0,3),'q1':(0,1,-1),'q1^2':(0,2,-2),'q1^3':(0,3,-3),'q1^4':(0,4,-4),'E':(0,1,1),
    'F':(10,-1,5),'C':(1,0,0),'A':(2,0,0),'Ad':(2,0,1),'A2d2':(4,0,2),'A4d4':(8,0,4)}
X=[(0,0,k) for k in range(9)]
def one(args):
    N,b12,b,budget=args
    T=[(0,23,b12),(0,46,2*b12),(0,2*N-1,b),(0,2*(2*N-1),2*b),(0,3*(2*N-1),3*b)]
    inp=f"3 {len(S0)}\n"+"\n".join(' '.join(map(str,v)) for v in S0.values())+f"\n{len(X)}\n"+"\n".join(' '.join(map(str,v)) for v in X)+f"\n{len(T)}\n"+"\n".join(' '.join(map(str,v)) for v in T)+f"\n{budget}\n"
    return args, subprocess.run(['./search'],input=inp,capture_output=True,text=True).stdout
if __name__=='__main__':
    jobs=[tuple(map(int,j.split(','))) for j in sys.argv[1:]]
    with ThreadPoolExecutor(len(jobs)) as ex:
        for a,out in ex.map(one,jobs): print('N,b12,b,budget=',a,out.strip(),flush=True)
