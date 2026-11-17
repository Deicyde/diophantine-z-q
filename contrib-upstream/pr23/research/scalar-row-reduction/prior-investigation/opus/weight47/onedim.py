"""1D relaxation: track only ell-degree (sum of orders at the five roots of F), unit = 1/5 of an e.
Every monomial model (e,delta,A,C, affine products of linear factors, F, degree<=8 Q's) projects here.
Base: q1^k -> -5k (k=1..4), E -> -5, F -> +5, affine products of <=3 linear factors -> 0..3, A-items -> 0.
Extra quadratic Q: degree<=8 polynomials -> 0..8. Gate v = x+y-z. Targets: -5*{23,46,2N-1,2(2N-1),3(2N-1)}."""
import sys
def solve(N,budget,withF=True,ell=True):
    base={-5,-10,-15,-20,0}|({5} if withF else set())|({1,2,3} if ell else set())
    X=set(range(0,9)) if ell else {0}
    T=[-5*a for a in (23,46,2*N-1,2*(2*N-1),3*(2*N-1))]
    def reach(S):
        L=sorted(S); Q={a+b for i,a in enumerate(L) for b in L[i:]}|X
        return {q-z for q in Q for z in L}
    seen=set()
    def dfs(S,used):
        S=set(S); ch=True
        while ch:
            ch=False; R=reach(S)
            for t in T:
                if t not in S and t in R: S.add(t); used+=1; ch=True
        miss=sum(t not in S for t in T)
        if miss==0: return used<=budget
        if used+miss+1>budget: return False
        key=frozenset(S)
        if key in seen: return False
        seen.add(key)
        for c in reach(S)-S:
            if dfs(S|{c},used+1): return True
        return False
    return dfs(base,0)
if __name__=='__main__':
    for budget,Ns in [(6,range(13,52)),(7,range(47,52))]:
        for withF in (True,False):
            res={N:solve(N,budget,withF) for N in Ns}
            print('budget',budget,'F' if withF else 'noF','feasible N:',[N for N,v in res.items() if v])
