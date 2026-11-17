import subprocess, sys
# r=0 lattice: delta^beta F^gamma ; e = delta^5/F
def em(a,b):  # e^a delta^b
    return (5*a+b, -a)
S0 = {'d':(1,0),'d2':(2,0),'d3':(3,0),'F':(0,1),'q1':em(1,-1),'q1^2':em(2,-2),'q1^3':em(3,-3),'q1^4':em(4,-4),'E':em(1,1)}
def run(N, budget, extra=True, S0=S0, extraQ=None):
    T=[em(23,-1),em(46,-2),em(2*N-1,-1),em(2*(2*N-1),-2),em(3*(2*N-1),-3)]
    if extraQ is None: extraQ=[(k,0) for k in range(0,9)] if extra else []
    inp=f"2 {len(S0)}\n"+"\n".join(f"{a} {b}" for a,b in S0.values())+f"\n{len(extraQ)}\n"+"\n".join(f"{a} {b}" for a,b in extraQ)+f"\n{len(T)}\n"+"\n".join(f"{a} {b}" for a,b in T)+f"\n{budget}\n"
    r=subprocess.run(['./search'],input=inp,capture_output=True,text=True)
    return r.stdout
if __name__=='__main__':
    N=int(sys.argv[1]); b=int(sys.argv[2]); ex=sys.argv[3]=='1'
    print(run(N,b,ex))
