# theta > 1: 30 random (beta, theta) with theta a product of 1-3 primes, theta = 1 mod 24,
# (beta/t) = 1 for t | theta and theta a square mod every q | beta; search n with the matrix
# conditions for n and n*theta.
import sys, random
sys.path.insert(0,'scratch/pc-from-rc')
from selmer import factor, leg, matrix_conditions
from construct import trial, isprime
rnd=random.Random(11)
primes=[p for p in range(5,600) if isprime(p)]
samples=[]
while len(samples)<30:
    k=rnd.choice([1,2,2,3]); qs=rnd.sample(primes[:60],k); beta=1
    for q in qs: beta*=q
    if beta%24!=17: continue
    good=[t for t in primes if beta%t and leg(beta,t)==0]
    for _ in range(2000):
        j=rnd.choice([1,2,3]); ts=rnd.sample(good,j); th=1
        for t in ts: th*=t
        if th%24==1 and all(sum(leg(t,q) for t in ts)%2==0 for q in qs):
            samples.append((beta,th)); break
fails=0
for beta,theta in samples:
    r=trial(beta,theta,tries=20000)
    if r is None: fails+=1
    print(beta,factor(beta),theta,factor(theta),"->",r,flush=True)
print("fails",fails)
