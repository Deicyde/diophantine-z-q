import sys, pickle; sys.path.insert(0, '.')
from poly import *
N, Y, D, T, cls = pickle.load(open('/tmp/igs_t4.pkl', 'rb'))
out = []
for i, t in enumerate(T):
    out.append('def T%d {K : Type*} [Field K] (e1 e2 e3 : K) : K :=\n    %s\n' % (i+1, lean_poly(t, ['e1', 'e2', 'e3'])))
open('gen_T.lean', 'w').write('\n'.join(out))
print('\n'.join(out))
