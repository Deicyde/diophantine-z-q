# Search for n = beta * (aux primes) with the matrix conditions for n and n*theta
# (ker K = <1, 1_beta>, lambda not in im K), following the slot shape of L1040-1046:
# d-1 aux primes = 1 mod 12 (type (0,0)) and one q0 = 7 mod 12 (type (1,1)), d = omega(beta).
import sys, random, itertools
sys.path.insert(0, 'scratch/pc-from-rc')
from selmer import factor, leg, matrix_conditions, selmer
def isprime(n):
    if n<2: return False
    i=2
    while i*i<=n:
        if n%i==0: return False
        i+=1
    return True
P1=[p for p in range(13,3000) if isprime(p) and p%12==1]
P7=[p for p in range(7,3000) if isprime(p) and p%12==7]
def trial(beta,theta,tries=20000,seed=1):
    rnd=random.Random(seed)
    qb=factor(beta); d=len(qb); qt=factor(theta) if theta>1 else []
    bad=set(qb)|set(qt)|{2,3}
    for t in range(tries):
        aux=rnd.sample([p for p in P1 if p not in bad],d-1)
        q0=rnd.choice([p for p in P7 if p not in bad])
        n=beta*q0
        for p in aux: n*=p
        if n%12!=11: continue
        k1,l1,_=matrix_conditions(n,beta)
        if not(k1 and l1): continue
        k2,l2,_=matrix_conditions(n*theta,beta)
        if k2 and l2: return n,t
    return None
if __name__=="__main__":
    for beta,theta in [(17,1),(41,1),(17,13*101),(89,1),(17*41,1),(17*41,73),(5*7*13*... if False else 17*137,1),(65,1),(65,97*193)]:
        if beta%24!=17 or theta%24!=1: print("skip",beta,theta); continue
        # bookkeeping local-square conditions
        ok=all(leg(beta,p)==0 for p in factor(theta)) if theta>1 else True
        ok=ok and (all(leg(theta,q)==0 for q in factor(beta)) if theta>1 else True)
        print(beta,theta,"bookkeeping-ok" if ok else "bookkeeping-FAIL", trial(beta,theta))
