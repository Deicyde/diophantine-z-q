import sys, pickle; sys.path.insert(0, '.')
from poly import *
N, Y, D, T, cls = pickle.load(open('/tmp/igs_t4.pkl', 'rb'))
names = ['e1', 'e2', 'e3']
chunks = {1: [], 2: [], 3: ['_0', '_1', '_2', '_3', '_4']}
out = []
for i in range(3):
    for j in range(3):
        nm = 'y%dc%d' % (i+1, j)
        extra = ', '.join(nm + s for s in chunks[i+1])
        out.append('''set_option maxHeartbeats 4000000 in
theorem %s_Ne {K : Type*} [Field K] (e1 e2 e3 : K) :
    %s (Ne e1 e2 e3) =
    %s := by
  simp only [%s, Ne, Matrix.cons_val]
  ring
''' % (nm, nm, lean_poly(Y[i][j], names), nm + (', ' + extra if extra else '')))
open('gen_yNe.lean', 'w').write('\n'.join(out))
