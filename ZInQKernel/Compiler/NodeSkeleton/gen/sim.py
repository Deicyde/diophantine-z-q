import re, sys
import os
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'Universal', 'Interpreter.lean')).read()
body = src[src.index('def interpreter : Program := ['):]
body = re.sub(r'/-.*?-/', '', body, flags=re.S)
prog = []
for m in re.finditer(r'\.(inc|dec|halt)((?:\s+\d+)*)', body):
    args = list(map(int, m.group(2).split()))
    prog.append((m.group(1),) + tuple(args))
assert len(prog) == 1399, len(prog)

class B:
    def __init__(s, k, trace=False):
        s.next = k; s.table = {}; s.nodes = [('var', i) for i in range(k)]
        s.trace = [] if trace else None
        s.ctx = None
    def node(s, n):
        j = s.table.get(n)
        if j is not None:
            if s.trace is not None: s.trace.append((len(s.nodes), n, j, s.ctx))
            return j
        j = len(s.nodes); s.table[n] = j; s.nodes.append(n)
        if s.trace is not None: s.trace.append((j, n, None, s.ctx))
        return j
    def fresh(s):
        j = len(s.nodes); s.nodes.append(('var', s.next)); s.next += 1; return j
    def constant(s, c): return s.node(('const', c))
    def addL(s, xs):
        if not xs: return s.constant(0)
        acc = xs[0]
        for y in xs[1:]: acc = s.node(('add', acc, y))
        return acc
    def mulL(s, xs):
        if not xs: return s.constant(1)
        acc = xs[0]
        for y in xs[1:]: acc = s.node(('mul', acc, y))
        return acc
    def square(s, x): return s.mulL([x, x])
    def scale(s, n, x):
        c = s.constant(n); return s.mulL([c, x])
    def power(s, P, Q, R):
        j = len(s.nodes); s.nodes.append(('call', P, Q, R, s.next)); s.next += 79; return ('call', j)
    def lt(s, a, b):
        d = s.fresh(); c1 = s.constant(1); e = s.addL([a, c1, d]); return ('eq', b, e)
    def odd(s, x):
        h = s.fresh(); t = s.scale(2, h); c1 = s.constant(1); e = s.addL([t, c1]); return ('eq', x, e)
    def binomial(s, C, N, K):
        base = s.fresh(); total = s.fresh(); place = s.fresh(); q = s.fresh(); r = s.fresh()
        fs = []
        c2 = s.constant(2); c1 = s.constant(1); a = s.addL([N, c1]); fs.append(s.power(base, c2, a))
        c1 = s.constant(1); a = s.addL([base, c1]); fs.append(s.power(total, a, N))
        fs.append(s.power(place, base, K))
        fs.append(s.lt(C, base))
        fs.append(s.lt(r, place))
        m1 = s.mulL([base, q]); a1 = s.addL([m1, C]); m2 = s.mulL([place, a1]); a2 = s.addL([m2, r])
        fs.append(('eq', total, a2))
        return ('and', fs)
    def orthogonal(s, a, b):
        c = s.fresh(); n = s.addL([a, b]); f1 = s.binomial(c, n, a); f2 = s.odd(c); return ('and', [f1, f2])
    def mask(s, a, b):
        c = s.fresh(); f1 = s.binomial(c, b, a); f2 = s.odd(c); return ('and', [f1, f2])
    def bitAnd(s, z, x, y):
        a = s.fresh(); b = s.fresh()
        f1 = ('eq', x, s.addL([z, a])); f2 = ('eq', y, s.addL([z, b]))
        return ('and', [f1, f2, s.orthogonal(z, a), s.orthogonal(z, b), s.orthogonal(a, b)])
    def encode(s, f):
        t = f[0]
        if t == 'eq':
            m = s.scale(-1, f[2]); return s.addL([f[1], m])
        if t == 'call': return f[1]
        if t == 'and':
            es = [s.encode(g) for g in f[1]]
            sq = [s.square(e) for e in es]
            return s.addL(sq)
        raise Exception(t)

def construction(s, p, r, k, mark=None):
    mark = mark or (lambda name: None)
    a = list(range(k))
    zero = s.constant(0); one = s.constant(1)
    q, c, K, B_, T, F, D = [s.fresh() for _ in range(7)]
    R = [s.fresh() for _ in range(r)]; N = [s.fresh() for _ in range(r)]; S = [s.fresh() for _ in range(len(p))]
    fs = []
    mark('items1')
    fs.append(s.lt(zero, c)); c2 = s.constant(2); fs.append(s.power(K, c2, c))
    e = s.scale(4, K); fs.append(('eq', B_, e))
    cl = s.constant(len(p)); fs.append(s.lt(cl, B_)); fs.append(s.power(T, B_, q))
    for ai in a: fs.append(s.lt(ai, K))
    mark('items2')
    m1 = s.mulL([B_, F]); a1 = s.addL([m1, one]); m2 = s.mulL([B_, T]); a2 = s.addL([F, m2]); fs.append(('eq', a1, a2))
    a1 = s.addL([D, F]); m = s.mulL([K, F]); fs.append(('eq', a1, m))
    a1 = s.addL(S); fs.append(('eq', a1, F))
    fs.append(('eq', S[-1] if S else zero, T))
    mark('items3')
    for x in S: fs.append(s.mask(x, F))
    mark('items4')
    for j in range(r):
        Rj, Nj = R[j], N[j]
        fs.append(s.mask(Rj, D)); fs.append(s.lt(Rj, T))
        x = s.mulL([K, Nj]); y = s.addL([Rj, D]); z = s.mulL([K, F]); fs.append(s.bitAnd(x, y, z))
    mark('items5')
    vw = {}
    for i, ins in enumerate(p):
        if ins[0] == 'dec':
            j = ins[1]; V = s.fresh(); W = s.fresh()
            fs.append(s.bitAnd(V, S[i], N[j] if j < r else zero))
            e = s.addL([V, W]); fs.append(('eq', S[i], e))
            vw.setdefault(i, (V, W))
    mark('items6')
    for j in range(r):
        decs = [vw.get(i, (zero, zero))[0] for i, ins in enumerate(p) if ins[0] == 'dec' and ins[1] == j]
        incs = [S[i] for i, ins in enumerate(p) if ins[0] == 'inc' and ins[1] == j]
        ij = a[j] if j < k else zero
        s1 = s.addL(decs); m1 = s.mulL([B_, s1]); l = s.addL([R[j], m1])
        m2 = s.mulL([B_, R[j]]); s2 = s.addL(incs); m3 = s.mulL([B_, s2]); rr = s.addL([ij, m2, m3])
        fs.append(('eq', l, rr))
    mark('items7')
    for i in range(len(p)):
        ins_ = []
        for i2, ins in enumerate(p):
            if ins[0] == 'inc' and ins[2] == i: ins_.append(S[i2])
            if ins[0] == 'dec':
                if ins[2] == i: ins_.append(vw.get(i2, (zero, zero))[0])
                if ins[3] == i: ins_.append(vw.get(i2, (zero, zero))[1])
        sm = s.addL(ins_); m = s.mulL([B_, sm]); rr = s.addL([one if i == 0 else zero, m])
        fs.append(('eq', S[i], rr))
    mark('encode')
    return ('and', fs)

if __name__ == '__main__':
    s = B(2)
    phi = construction(s, prog, 204, 2)
    E0 = len(s.nodes)
    s.encode(phi)
    from collections import Counter
    cnt = Counter(n[0] for n in s.nodes)
    print(len(s.nodes), cnt, 'E0', E0)
