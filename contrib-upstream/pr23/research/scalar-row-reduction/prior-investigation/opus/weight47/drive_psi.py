import subprocess, sys
# psi relaxation: (ord at delta-root, total ord at roots of F). e=delta^5/F -> (5,-5)
def em(a,b): return (5*a+b, -5*a)
S0={}
for i in range(4):
    for j in range(4-i):
        if i+j>0: S0[f'd^{i}l^{j}']=(i,j)
S0.update({'F':(0,5),'q1':em(1,-1),'q1^2':em(2,-2),'q1^3':em(3,-3),'q1^4':em(4,-4),'E':em(1,1)})
def run(N,budget,extra=True):
    T=[em(23,-1),em(46,-2),em(2*N-1,-1),em(2*(2*N-1),-2),em(3*(2*N-1),-3)]
    X=[(i,j) for i in range(9) for j in range(9-i)] if extra else []
    inp=f"2 {len(S0)}\n"+"\n".join(f"{a} {b}" for a,b in S0.values())+f"\n{len(X)}\n"+"\n".join(f"{a} {b}" for a,b in X)+f"\n{len(T)}\n"+"\n".join(f"{a} {b}" for a,b in T)+f"\n{budget}\n"
    return subprocess.run(['./search'],input=inp,capture_output=True,text=True).stdout
if __name__=='__main__':
    print(run(int(sys.argv[1]),int(sys.argv[2]),sys.argv[3]=='1'))
