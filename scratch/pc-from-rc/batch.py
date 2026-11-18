# 30 random (beta, theta) satisfying the bookkeeping conditions; search n; brute-force check small cases.
import sys, random
sys.path.insert(0,'scratch/pc-from-rc')
from selmer import factor, leg, matrix_conditions, selmer
from construct import trial, isprime
rnd=random.Random(7)
primes=[p for p in range(5,400) if isprime(p)]
samples=[]
while len(samples)<30:
    k=rnd.choice([1,1,2,2,3])
    qs=rnd.sample(primes,k); beta=1
    for q in qs: beta*=q
    if beta%24!=17: continue
    # theta: product of 0-2 primes not dividing beta, = 1 mod 24, with mutual local squares
    j=rnd.choice([0,1,2]); theta=1
    if j:
        ts=rnd.sample([p for p in primes if beta%p], j)
        theta=1
        for t in ts: theta*=t
        if theta%24!=1: continue
        if not all(leg(beta,p)==0 for p in ts): continue
        if not all(leg(theta,q)==0 for q in qs): continue
    samples.append((beta,theta))
for beta,theta in samples:
    r=trial(beta,theta,tries=5000)
    line=f"{beta} {factor(beta)} theta={theta} -> {r}"
    if r and r[0]<20000:
        S=selmer(r[0]); line+=f" brute #Sel(n)={len(S)} beta-in={(beta,1) in S}"
    print(line, flush=True)
