# Normalization-freedom model: q_m = e^(2m-1) delta^b with b negative odd (D' = delta^k D, k<=1).
import subprocess, sys, itertools
from concurrent.futures import ThreadPoolExecutor
from drive import em, S0
def inp(N,b12,b,budget):
    T=[em(23,b12),em(46,2*b12),em(2*N-1,b),em(2*(2*N-1),2*b),em(3*(2*N-1),3*b)]
    X=[(k,0) for k in range(9)]
    return f"2 {len(S0)}\n"+"\n".join(f"{a} {c}" for a,c in S0.values())+f"\n{len(X)}\n"+"\n".join(f"{a} {c}" for a,c in X)+f"\n{len(T)}\n"+"\n".join(f"{a} {c}" for a,c in T)+f"\n{budget}\n"
def one(args):
    N,b12,b,budget=args
    out=subprocess.run(['./search'],input=inp(N,b12,b,budget),capture_output=True,text=True).stdout
    return (N,b12,b,budget,out)
if __name__=='__main__':
    N=int(sys.argv[1]); budget=int(sys.argv[2])
    B12=[int(x) for x in sys.argv[3].split(',')]; B=[int(x) for x in sys.argv[4].split(',')]
    jobs=[(N,b12,b,budget) for b12 in B12 for b in B]
    with ThreadPoolExecutor(int(sys.argv[5]) if len(sys.argv)>5 else 12) as ex:
        for N,b12,b,bu,out in ex.map(one,jobs):
            print(f"N={N} b12={b12} b={b} budget={bu}: "+out.strip().replace('\n','\n   '),flush=True)
