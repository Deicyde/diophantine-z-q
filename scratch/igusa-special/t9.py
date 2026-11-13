import sys, pickle; sys.path.insert(0, '.')
from poly import *
nv = 4
l, m, n, sg = [var(i, nv) for i in range(4)]
one = const(1, nv); c = lambda x: const(x, nv)
e1 = add(add(l, m), n); e2 = add(add(mul(l, m), mul(l, n)), mul(m, n)); e3 = mul(mul(l, m), n)
Nr = [{}, e3, scal(-1, add(e2, e3)), add(e1, e2), scal(-1, add(one, e1)), one, {}]
classes = [
  ('1', sub(mul(m, n), l), {}, l),
  ('2', add(sub(sub(l, m), n), mul(m, n)), one, sub(one, l)),
  ('3', add(sub(sub(l, mul(l, m)), mul(l, n)), mul(m, n)), l, mul(l, sub(l, one))),
  ('4', add(sub(sub(mul(l, m), l), mul(l, n)), n), l, mul(l, sub(l, m))),
]
res = {}
for name, D, p, k in classes:
    a, b, cc, d = sub(sg, p), add(p, sg), c(-1), one
    g = actC_poly(Nr, a, b, cc, d, one, nv)
    hs = sub(mul(sg, sg), k)
    certs = {}
    for i in (1, 3, 5):
        q1, r1 = divmod_lex(g[i], hs, [3, 0, 1, 2])
        # r1 has deg_sigma <= 1; divide by D (lex order chosen so D's lead term is clean)
        q2, r2 = divmod_lex(r1, D, [2, 1, 0, 3] if name in '34' else [0, 1, 2, 3])
        assert not r2, (name, i, len(r2))
        assert sub(g[i], add(mul(q1, hs), mul(q2, D))) == {}
        certs[i] = (q1, q2)
    even = {i: divmod_lex(g[i], hs, [3, 0, 1, 2])[1] for i in (0, 2, 4, 6)}
    print(name, 'certs sizes', {i: (len(a), len(b)) for i, (a, b) in certs.items()}, 'even sizes', {i: len(v) for i, v in even.items()})
    res[name] = (D, p, k, certs, g)
pickle.dump(res, open('/tmp/igs_t9.pkl', 'wb'))
