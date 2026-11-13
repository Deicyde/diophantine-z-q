"""Minimal sparse multivariate polynomials over Q (pure python; no sympy on this host).
A polynomial is a dict {exponent tuple: Fraction}. nv = number of variables."""
from fractions import Fraction as F
import re
ROOT = __file__.rsplit('/scratch/', 1)[0]

def const(c, nv): return {(0,)*nv: F(c)} if c else {}
def var(i, nv):
    e = [0]*nv; e[i] = 1; return {tuple(e): F(1)}
def add(p, q):
    r = dict(p)
    for k, v in q.items():
        s = r.get(k, 0) + v
        if s: r[k] = s
        else: r.pop(k, None)
    return r
def scal(c, p):
    c = F(c); return {k: c*v for k, v in p.items()} if c else {}
def sub(p, q): return add(p, scal(-1, q))
def mul(p, q):
    r = {}
    for k1, v1 in p.items():
        for k2, v2 in q.items():
            k = tuple(a+b for a, b in zip(k1, k2))
            s = r.get(k, 0) + v1*v2
            if s: r[k] = s
            else: r.pop(k, None)
    return r
def pw(p, n, nv):
    r = const(1, nv)
    for _ in range(n): r = mul(r, p)
    return r
def ev(p, pt):
    s = F(0)
    for k, v in p.items():
        t = v
        for x, e in zip(pt, k):
            if e: t *= F(x)**e
        s += t
    return s
def subst(p, imgs, nv):
    """substitute variable i -> imgs[i] (polys in nv vars)"""
    cache = {}
    def pwc(i, e):
        if (i, e) not in cache: cache[(i, e)] = pw(imgs[i], e, nv)
        return cache[(i, e)]
    r = {}
    for k, v in p.items():
        t = const(v, nv)
        for i, e in enumerate(k):
            if e: t = mul(t, pwc(i, e))
        r = add(r, t)
    return r
def deg(p, i): return max((k[i] for k in p), default=-1)

# ---- parse Lean defs ----
def lean_defs(path):
    src = open(path).read()
    out = {}
    for m in re.finditer(r'^def (\w+) [^\n]*?:=\n?(.*?)(?=\n\n|\n/--|\ndef |\ntheorem |\Z)', src, re.S | re.M):
        out[m.group(1)] = m.group(2)
    return out
def lean_expr_to_poly(body, env):
    """body: Lean expression in a 0..a 6 with rational literals; env: name -> poly (in 7 vars)"""
    s = body
    s = re.sub(r'\(\((-?\d+) : [KR]\) / (\d+)\)', r'F(\1,\2)', s)
    s = re.sub(r'\((-?\d+) : [KR]\)', r'F(\1)', s)
    s = re.sub(r'\b(\w+) a\b', lambda m: 'E["%s"]' % m.group(1) if m.group(1) in env else m.group(0), s)
    s = re.sub(r'\ba (\d)\b', r'A[\1]', s)
    s = s.replace('^', '**')
    return eval('(' + s + ')', {'F': F, 'A': [P(var(i, 7)) for i in range(7)], 'E': {k: P(v) for k, v in env.items()}}).d

class P:
    """operator wrapper used only for parsing"""
    def __init__(s, d): s.d = d
    def __add__(s, o): return P(add(s.d, o.d if isinstance(o, P) else const(o, 7)))
    __radd__ = __add__
    def __sub__(s, o): return P(sub(s.d, o.d if isinstance(o, P) else const(o, 7)))
    def __rsub__(s, o): return P(sub(const(o, 7), s.d))
    def __neg__(s): return P(scal(-1, s.d))
    def __mul__(s, o): return P(mul(s.d, o.d) if isinstance(o, P) else scal(o, s.d))
    __rmul__ = __mul__
    def __pow__(s, n): return P(pw(s.d, n, 7))

def load_y():
    g = lean_defs(ROOT + '/ZInQKernel/HDecomp/Textbook/Igusa/Generic.lean')
    env = {}
    names = [n for n in g if re.match(r'y\dc\d(_\d)?$', n)]
    names.sort(key=lambda n: (len(n) == 4, n))
    for n in names: env[n] = lean_expr_to_poly(g[n], env)
    return [[env['y%dc%d' % (i, k)] for k in range(3)] for i in (1, 2, 3)]

def load_J():
    g = lean_defs(ROOT + '/ZInQKernel/HDecomp/Textbook/Igusa/Forward.lean')
    J = [lean_expr_to_poly(g[n], {}) for n in ('J2', 'J4', 'J6')]
    src = open(ROOT + '/ZInQKernel/HDecomp/Textbook/Igusa/Forward.lean').read()
    blk = src.split('def j10Data')[1].split('def J10')[0]
    j10 = {}
    for c, ex in re.findall(r'\((-?\d+), \[([\d, ]+)\]\)', blk):
        j10[tuple(int(t) for t in ex.split(','))] = F(int(c))
    J.append(j10)
    return J

def sym_to_e(p):
    """p symmetric in 3 vars -> poly in (e1,e2,e3); standard leading-term algorithm"""
    p = dict(p); out = {}
    e = [ {(1,0,0):F(1),(0,1,0):F(1),(0,0,1):F(1)}, {(1,1,0):F(1),(1,0,1):F(1),(0,1,1):F(1)}, {(1,1,1):F(1)} ]
    while p:
        k = max(p); c = p[k]
        a, b, cc = k
        assert a >= b >= cc, ('not symmetric', k)
        ex = (a-b, b-cc, cc)
        out[ex] = out.get(ex, 0) + c
        t = const(c, 3)
        for i, n in enumerate(ex):
            for _ in range(n): t = mul(t, e[i])
        p = sub(p, t)
    return out

def fmt(p, names):
    terms = []
    for k in sorted(p, reverse=True):
        mon = '*'.join(('%s^%d' % (n, e) if e > 1 else n) for n, e in zip(names, k) if e)
        terms.append('(%s)%s' % (p[k], '*' + mon if mon else ''))
    return ' + '.join(terms) if terms else '0'

def lean_num(c):
    c = F(c)
    if c.denominator == 1: return '(%d : K)' % c.numerator
    return '((%d : K) / %d)' % (c.numerator, c.denominator)
def lean_poly(p, names, width=95, indent='    '):
    if not p: return '0'
    terms = []
    for k in sorted(p, reverse=True):
        c = p[k]
        mon = [('%s ^ %d' % (n, e) if e > 1 else n) for n, e in zip(names, k) if e]
        if mon:
            if c == 1: s = ' * '.join(mon)
            elif c == -1: s = '-' + ' * '.join(mon) if False else '(-1 : K) * ' + ' * '.join(mon)
            else: s = lean_num(c) + ' * ' + ' * '.join(mon)
        else: s = lean_num(c)
        terms.append(s)
    out, line = [], ''
    for i, t in enumerate(terms):
        piece = t if i == 0 else ' + ' + t
        if line and len(line) + len(piece) > width:
            out.append(line + ' +'); line = indent + t
        else: line += piece
    out.append(line)
    return '\n'.join(out)

def divmod_lex(p, d, order):
    """divide p by d under lex order given by variable priority list `order`; returns (q, r)"""
    key = lambda k: tuple(k[i] for i in order)
    lt = max(d, key=key); lc = d[lt]
    q, r, p = {}, {}, dict(p)
    while p:
        k = max(p, key=key); c = p[k]
        if all(a >= b for a, b in zip(k, lt)):
            mon = {tuple(a - b for a, b in zip(k, lt)): c / lc}
            q = add(q, mon); p = sub(p, mul(mon, d))
        else:
            r[k] = c; del p[k]
    return q, r

def actC_poly(f, a, b, c, d, e, nv):
    """coefficients of e * sum_k f_k (aX+b)^k (cX+d)^(6-k) ; f list of 7 polys"""
    def upol_mul(P, Q):
        R = [{} for _ in range(len(P) + len(Q) - 1)]
        for i, x in enumerate(P):
            for j, y in enumerate(Q): R[i+j] = add(R[i+j], mul(x, y))
        return R
    out = [{} for _ in range(7)]
    for k in range(7):
        if not f[k]: continue
        t = [f[k]]
        for _ in range(k): t = upol_mul(t, [b, a])
        for _ in range(6 - k): t = upol_mul(t, [d, c])
        for i in range(len(t)): out[i] = add(out[i], mul(e, t[i]))
    return out
