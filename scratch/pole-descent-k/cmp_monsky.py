import sys, random, math
sys.path.insert(0,'../rs-pole')
import selmer_descent as sd
import monsky
rng=random.Random(5)
bad=0;binding=0;tot=0
ns=[n for n in range(3,3000,2) if all(n%(p*p) for p in range(3,60,2))]
ns=ns[:150]+rng.sample([n for n in range(3001,200000,2) if all(n%(p*p) for p in (3,5,7,11,13,17,19,23))],80)
for n in ns:
    if any(n%(p*p)==0 for p in monsky.primes_of(n)): continue
    reps=monsky.selmer_reps(n)
    good=[r for r in reps if r[2]]
    if len(good)!=len(reps): binding+=1
    d,g,k=sd.selmer_dim(n,1,-1,rng)
    tot+=1
    if d!=2+int(math.log2(len(good))): bad+=1; print('MISMATCH',n,d,reps)
print('tested',tot,'mismatches',bad,'2-adic binding',binding)
