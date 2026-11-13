import sys, pickle; sys.path.insert(0, '.')
from poly import *
G = pickle.load(open('/tmp/igs_G.pkl', 'rb'))
nv = 3
u, r = var(0, nv), var(2, nv); one = const(1, nv)
Q = add(sub(mul(pw(r, 2, nv), mul(u, u)), mul(mul(r, add(c32 := const(32, nv), scal(2, r))), u)), pw(sub(const(16, nv), r), 2, nv))
cand = scal(-2**38, mul(pw(r, 4, nv), mul(pw(sub(one, r), 3, nv), Q)))
print(sub(G, cand))
