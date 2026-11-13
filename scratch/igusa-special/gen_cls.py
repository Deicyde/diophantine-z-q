import sys, pickle; sys.path.insert(0, '.')
from poly import *
res = pickle.load(open('/tmp/igs_t9.pkl', 'rb'))
names = ['l', 'm', 'n', 's']
out = []
for name, (D, p, k, certs, g) in res.items():
    P = lean_poly(p, names) if p else '0'
    out.append('/-- Syntheme class %s: `D = %s`, involution with centre `p = %s`, `k = %s`. -/' % (name, lean_poly(D, names, 200), P, lean_poly(k, names, 200)))
    out.append('def D%s {K : Type*} [Field K] (l m n : K) : K := %s\n' % (name, lean_poly(D, names, 200)))
    out.append('def P%s {K : Type*} [Field K] (l m n : K) : K := %s\n' % (name, P))
    out.append('def K%s {K : Type*} [Field K] (l m n : K) : K := %s\n' % (name, lean_poly(k, names, 200)))
    for i, (q1, q2) in certs.items():
        out.append('''theorem cls%s_odd%d {K : Type*} [Field K] (l m n s : K) (hs : s ^ 2 = K%s l m n)
    (hD : D%s l m n = 0) :
    actC (Nr l m n) (s - P%s l m n) (P%s l m n + s) (-1) 1 1 %d = 0 := by
  simp only [actC, Nr, Matrix.cons_val, K%s, D%s, P%s] at *
  linear_combination (%s) * hs + (%s) * hD
''' % (name, i, name, name, name, name, i, name, name, name, lean_poly(q1, names, 400), lean_poly(q2, names, 400)))
open('gen_cls.lean', 'w').write('\n'.join(out))
