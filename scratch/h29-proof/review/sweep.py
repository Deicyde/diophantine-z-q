import sys
sys.path.insert(0, '/home/jackmccarthy/dzq-wt/h29-proof/scratch/h29-proof')
import genus_check as g
def sqf(n):
    d=2
    while d*d<=n:
        if n%(d*d)==0: return False
        d+=1
    return True
lo, hi, nt = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
ns=[n for n in range(lo,hi) if n%8 in (1,3) and sqf(n) and n>3]
g.run(ns, ntau=nt)
