# Generator of the pinned data (`Data/`), the chunk theorems and the assembly proof
# (`Final.lean`) of ZInQKernel/Compiler/NodeSkeleton. Run `python3 gen/gen.py` from anywhere;
# it rewrites `Data/*.lean` and `Final.lean`. The files `sim.py` (a Python transcription of the
# fast builder), `oracle.py` (the oracle: codes, hubs, far lanes) and `hsim.py` (a Python mirror
# of the checking builder of `Core.lean`) are its helpers.
import os, sys
from sim import prog
from oracle import run_full, make_oracle, LANEBASE
from hsim import HS, HB

OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')  # ZInQKernel/Compiler/NodeSkeleton
WK = 20            # pinned window length
TARGET = 5500      # nodes per chunk
NL = 5             # lanes

s0, phi0, E0 = run_full()
codes, hubs, lanes = make_oracle(s0, E0)
assert len(lanes) == NL
assert all(h // 8 >= 2 for h in hubs)

st = HS(2, 2, 0, 0, [], [2 * (5 * 1 + 2), 2 * (5 * 0 + 2)], [], codes, hubs, lanes)
hb = HB(st); hb.verbose = True; hb.scancost = 0; hb.hotcost = 0

zero, one, q, c, K, B, T, F, D = range(2, 11)
R = list(range(11, 215)); N = list(range(215, 419)); S = list(range(419, 1818))
RL, NL_, SL = "List.range' 11 204", "List.range' 215 204", "List.range' 419 1399"

def snap():
    return dict(len=st.len, next=st.next, adds=st.adds, muls=st.muls, consts=list(st.consts),
                win=st.win[:WK], hot=list(st.hot), ci=st.ci, hi=st.hi, li=list(st.li))

chunks = []   # dicts: name, kind, piece (Lean), outty, beq, out (python), start snap

def run_chunk(kind, piece, outty, fn, **extra):
    a = snap()
    out = fn()
    assert st.ok, kind
    chunks.append(dict(kind=kind, piece=piece, outty=outty, out=out, start=a, **extra))
    return out

# --- python mirrors of the pieces ---
def lf(f):
    """Lean syntax of a formula."""
    if f[0] == 'eq': return f'.eq {f[1]} {f[2]}'
    if f[0] == 'call': return f'.call {f[1]}'
    if f[0] == 'and': return '.and [' + ', '.join(lf(g) for g in f[1]) + ']'
    raise Exception(f)

def prelude():
    z = hb.constant(0); o = hb.constant(1)
    vs = [hb.fresh() for _ in range(7)]
    Rr = [hb.fresh() for _ in range(204)]; Nn = [hb.fresh() for _ in range(204)]
    Ss = [hb.fresh() for _ in range(1399)]
    assert [z, o] + vs == list(range(2, 11)) and Rr == R and Nn == N and Ss == S
    return None

def items1():
    fs = [hb.lt(zero, c)]
    c2 = hb.constant(2); fs.append(hb.power(K, c2, c))
    e = hb.scale(4, K); fs.append(('eq', B, e))
    cl = hb.constant(len(prog)); fs.append(hb.lt(cl, B)); fs.append(hb.power(T, B, q))
    for ai in range(2): fs.append(hb.lt(ai, K))
    return fs

def items2():
    fs = []
    m1 = hb.mulL([B, F]); a1 = hb.addL([m1, one]); m2 = hb.mulL([B, T]); a2 = hb.addL([F, m2])
    fs.append(('eq', a1, a2))
    a1 = hb.addL([D, F]); m = hb.mulL([K, F]); fs.append(('eq', a1, m))
    a1 = hb.addL(S); fs.append(('eq', a1, F))
    fs.append(('eq', S[-1], T))
    return fs

def regmasks(j):
    Rj, Nj = R[j], N[j]
    fs = [hb.mask(Rj, D), hb.lt(Rj, T)]
    x = hb.mulL([K, Nj]); y = hb.addL([Rj, D]); z = hb.mulL([K, F])
    fs.append(hb.bitAnd(x, y, z))
    return fs

vwAll = []
def subbranches(a, n):
    fs = []; vw = []
    for i in range(a, a + n):
        ins = prog[i]
        if ins[0] == 'dec':
            j = ins[1]; V = hb.fresh(); W = hb.fresh()
            fs.append(hb.bitAnd(V, S[i], N[j] if j < 204 else zero))
            e = hb.addL([V, W]); fs.append(('eq', S[i], e))
            vw.append((i, V, W))
    vwAll.extend(vw)
    return (fs, vw)

def items6():
    vwd = {}
    for (i, V, W) in vwAll: vwd.setdefault(i, (V, W))
    fs = []
    for j in range(204):
        decs = [vwd.get(i, (zero, zero))[0] for i, ins in enumerate(prog) if ins[0] == 'dec' and ins[1] == j]
        incs = [S[i] for i, ins in enumerate(prog) if ins[0] == 'inc' and ins[1] == j]
        ij = j if j < 2 else zero
        s1 = hb.addL(decs); m1 = hb.mulL([B, s1]); l = hb.addL([R[j], m1])
        m2 = hb.mulL([B, R[j]]); s2 = hb.addL(incs); m3 = hb.mulL([B, s2]); rr = hb.addL([ij, m2, m3])
        fs.append(('eq', l, rr))
    return fs

def items7():
    vwd = {}
    for (i, V, W) in vwAll: vwd.setdefault(i, (V, W))
    fs = []
    for i in range(len(prog)):
        ins_ = []
        for i2, ins in enumerate(prog):
            if ins[0] == 'inc' and ins[2] == i: ins_.append(S[i2])
            if ins[0] == 'dec':
                if ins[2] == i: ins_.append(vwd.get(i2, (zero, zero))[0])
                if ins[3] == i: ins_.append(vwd.get(i2, (zero, zero))[1])
        sm = hb.addL(ins_); m = hb.mulL([B, sm]); rr = hb.addL([one if i == 0 else zero, m])
        fs.append(('eq', S[i], rr))
    return fs

# --- the construction chunks ---
run_chunk('prelude', 'preludeHP 1399 204', 'pre', prelude)
run_chunk('items1', 'items1 interpreterL (List.range 2) 2 4 5 6 7 8', 'forms', items1)
run_chunk('items2', f'items2 2 3 6 7 8 9 10 ({SL})', 'forms', items2)

def split_by_nodes(units, cost, target):
    """Split a list of units into consecutive groups of about `target` nodes."""
    groups = []; cur = []; acc = 0
    for u in units:
        cur.append(u); acc += cost(u)
        if acc >= target: groups.append(cur); cur = []; acc = 0
    if cur:
        if groups and acc < target // 3: groups[-1].extend(cur)
        else: groups.append(cur)
    return groups

# measure unit costs on the reference run (node counts per mask etc. are fixed)
items3_groups = split_by_nodes(list(range(1399)), lambda u: 23, TARGET)
for g in items3_groups:
    a, n = g[0], len(g)
    run_chunk('items3', f"items3 9 (List.range' {419 + a} {n})", 'forms',
              lambda g=g: [hb.mask(S[x], F) for x in g], a=a, n=n)

items4_groups = split_by_nodes(list(range(204)), lambda u: 105, TARGET)
for g in items4_groups:
    a, n = g[0], len(g)
    run_chunk('items4', f"seqConcat ((List.range' {a} {n}).map fun j => registerMasks 6 10 8 9 (({RL}).getD j 2) (({NL_}).getD j 2))",
              'forms', lambda g=g: [f for j in g for f in regmasks(j)], a=a, n=n)

cost5 = lambda i: 80 if prog[i][0] == 'dec' else 0
items5_groups = split_by_nodes(list(range(1399)), cost5, TARGET)
for k, g in enumerate(items5_groups):
    a, n = g[0], len(g)
    last = (k == len(items5_groups) - 1)
    assert (a + n == 1399) == last
    prog_l = f"(interpreterL.drop {a})" if last else f"((interpreterL.drop {a}).take {n})"
    run_chunk('items5', f"subBranchesK 2 ({NL_}) {a} (List.range' {419 + a} {1399 - a}) {prog_l}",
              'sb', lambda a=a, n=n: subbranches(a, n), a=a, n=n, last=last)

nsb = len(items5_groups)
VW = None  # Lean term of the branch histories, set below
def vwterm(names):
    if len(names) == 1: return names[0]
    return f"{names[0]} ++ ({vwterm(names[1:])})"

constr = list(chunks)
# names
for idx, ch in enumerate(chunks): ch['idx'] = idx
sb_idx = [ch['idx'] for ch in chunks if ch['kind'] == 'items5']
VW = vwterm([f'vw_{i}' for i in sb_idx])
run_chunk('items6', f"items6K interpreterL 204 (List.range 2) 2 7 ({RL}) ({SL}) ({VW})", 'forms', items6)
chunks[-1]['idx'] = len(chunks) - 1
run_chunk('items7', f"items7K interpreterL 2 3 7 ({SL}) ({VW})", 'forms', items7)
chunks[-1]['idx'] = len(chunks) - 1
assert st.len == E0

# --- the formula tree ---
form_idx = [ch['idx'] for ch in chunks if ch['outty'] in ('forms', 'sb')]
def forms_of(i):
    ch = chunks[i]
    return ch['out'][0] if ch['outty'] == 'sb' else ch['out']
# φs = l1 ++ (l2 ++ (T3 ++ (T4 ++ (T5 ++ (l6 ++ l7)))))
def rnest(xs):
    if len(xs) == 1: return ('leaf', xs[0])
    return ('app', ('leaf', xs[0]), rnest(xs[1:]))
by = lambda kind: [ch['idx'] for ch in chunks if ch['kind'] == kind]
tree = ('app', ('leaf', by('items1')[0]),
        ('app', ('leaf', by('items2')[0]),
         ('app', rnest(by('items3')),
          ('app', rnest(by('items4')),
           ('app', rnest(by('items5')),
            ('app', ('leaf', by('items6')[0]), ('leaf', by('items7')[0])))))))

# encoding chunks in tree order
enc_of = {}
def leaves(t):
    if t[0] == 'leaf': return [t[1]]
    return leaves(t[1]) + leaves(t[2])
for i in leaves(tree):
    fs = forms_of(i)
    run_chunk('enc', f"LForm.encodeList {('outF_' if chunks[i]['outty'] == 'sb' else 'out_')}{i}", 'nats',
              lambda fs=fs: [hb.encode(f) for f in fs], src=i)
    chunks[-1]['idx'] = len(chunks) - 1
    enc_of[i] = len(chunks) - 1
def esterm(t):
    if t[0] == 'leaf': return f'out_{enc_of[t[1]]}'
    return f'({esterm(t[1])} ++ {esterm(t[2])})'
ES = esterm(tree)
sq_of = {}
for i in leaves(tree):
    e = enc_of[i]
    run_chunk('squares', f"seqM (out_{e}.map square)", 'nats',
              lambda e=e: [hb.square(x) for x in chunks[e]['out']], src=e)
    chunks[-1]['idx'] = len(chunks) - 1
    sq_of[i] = len(chunks) - 1
def sqterm(t):
    if t[0] == 'leaf': return f'out_{sq_of[t[1]]}'
    return f'({sqterm(t[1])} ++ {sqterm(t[2])})'
SQ = sqterm(tree)
sq_all = [x for i in leaves(tree) for x in chunks[sq_of[i]]['out']]
run_chunk('sum', f"addL {SQ}", 'nat', lambda: hb.addL(sq_all))
chunks[-1]['idx'] = len(chunks) - 1
sqidx = None
final = snap()
assert st.ok and st.adds == 125307 and st.muls == 98361 and st.len == 293568
assert st.ci == len(codes) and st.hi == len(hubs) and st.li == [len(l) for l in lanes]
print('chunks', len(chunks), 'scan', hb.scancost)

C = len(chunks)
starts = [ch['start'] for ch in chunks] + [final]
for k in range(C):
    chunks[k]['end'] = starts[k + 1]

# ---------------- Lean output ----------------
HDR = '''import ZInQKernel.Compiler.NodeSkeleton.Check

/-! Generated by `gen/gen.py`: {doc} -/

namespace ZInQ.Compiler.NodeSkeleton

noncomputable section

'''
FTR = '''
end

end ZInQ.Compiler.NodeSkeleton
'''

def natl(xs): return '[' + ', '.join(map(str, xs)) + ']'
def pairl(xs): return '[' + ', '.join(f'({a}, {b})' for a, b in xs) + ']'
def triplel(xs): return '[' + ', '.join(f'({a}, {b}, {c})' for a, b, c in xs) + ']'

def pack(xs, base, k):
    ws = []
    for i in range(0, len(xs), k):
        w = 0
        for j, x in enumerate(xs[i:i + k]):
            assert 0 <= x < base
            w += x * base ** j
        ws.append(w)
    return ws

def wrap(s, width=100):
    out = []; line = ''
    for tok in s.split(' '):
        if len(line) + len(tok) + 1 > width:
            out.append(line); line = '    ' + tok
        else:
            line = (line + ' ' + tok) if line else tok
    out.append(line)
    return '\n'.join(out)

datadir = os.path.join(OUT, 'Data')
os.makedirs(datadir, exist_ok=True)
files = []
def write(name, doc, body, imports=None):
    path = os.path.join(datadir, name + '.lean')
    hdr = HDR.format(doc=doc)
    if imports:
        hdr = hdr.replace('import ZInQKernel.Compiler.NodeSkeleton.Check\n',
                          'import ZInQKernel.Compiler.NodeSkeleton.Check\n' + ''.join(f'import ZInQKernel.Compiler.NodeSkeleton.Data.{m}\n' for m in imports))
    with open(path, 'w') as f:
        f.write(hdr + body + FTR)
    files.append(name)
    print(name, os.path.getsize(path))

# program
def li(ins):
    if ins[0] == 'inc': return f'.inc {ins[1]} {ins[2]}'
    if ins[0] == 'dec': return f'.dec {ins[1]} {ins[2]} {ins[3]}'
    return '.halt'
write('Program', 'the universal interpreter, transcribed.',
      '/-- The universal interpreter `𝒰` (a copy of `Universal.interpreter`). -/\ndef interpreterL : List LInstr :=\n  ' + wrap('[' + ', '.join(li(i) for i in prog) + ']') + '\n')

# oracle: hubs and lanes per chunk
body = ''
HB_BASE, HB_K = 1 << 24, 16
LB_BASE, LB_K = 1 << 64, 8
for k, ch in enumerate(chunks):
    a, e = ch['start'], ch['end']
    hs = hubs[a['hi']:e['hi']]
    body += f'/-- The hubs of chunk {k}. -/\ndef hubs_{k} : List Nat := unpack {HB_BASE} {HB_K} {len(hs)} {wrap(natl(pack(hs, HB_BASE, HB_K)))}\n\n'
    ls = []
    for l in range(NL):
        seg = lanes[l][a['li'][l]:e['li'][l]]
        ls.append(f'({len(seg)}, {natl(pack(seg, LB_BASE, LB_K))})')
    body += f'/-- The lanes of chunk {k}. -/\ndef lanes_{k} : List (List Nat) := unpackLanes {LB_BASE} {LB_K} {wrap("[" + ", ".join(ls) + "]")}\n\n'
body += '/-- The hubs of all chunks. -/\ndef hubsData : List (List Nat) := ' + wrap('[' + ', '.join(f'hubs_{k}' for k in range(C)) + ']') + '\n\n'
body += '/-- The lanes of all chunks. -/\ndef lanesData : List (List (List Nat)) := ' + wrap('[' + ', '.join(f'lanes_{k}' for k in range(C)) + ']') + '\n\n'
lims = [ch['end']['len'] for ch in chunks]
body += '/-- The length bounds of all chunks. -/\ndef limsData : List Nat := ' + wrap(natl(lims)) + '\n'
write('Oracle', 'the hubs and the far lanes of the chunks.', body)

# states
body = ''
def state(snp, lim):
    return (f"⟨{snp['len']}, {snp['next']}, {snp['adds']}, {snp['muls']}, {pairl(snp['consts'])}, "
            f"{natl(snp['win'])}, {pairl(snp['hot'])}, [], [], [], {lim}, true⟩")
for k in range(C + 1):
    lim = lims[k] if k < C else starts[C]['len']
    if k == 0:
        assert starts[0]['consts'] == [] and starts[0]['win'] == [14, 4] and starts[0]['len'] == 2
        body += f'/-- The pinned state at the start of chunk 0. -/\ndef st_0 : HState := stInit {lim}\n\n'
    else:
        body += f'/-- The pinned state at the start of chunk {k}. -/\ndef st_{k} : HState :=\n  {wrap(state(starts[k], lim))}\n\n'
write('States', 'the pinned states at the chunk boundaries.', body)

# chunk files
CODE_BASE, CODE_K = 16, 64
groups = []; cur = []; acc = 0
for k, ch in enumerate(chunks):
    nodes = ch['end']['len'] - ch['start']['len']
    if cur and acc + nodes > 4 * TARGET:
        groups.append(cur); cur = []; acc = 0
    cur.append(k); acc += nodes
groups.append(cur)
BEQ = {'pre': 'preludeBeq', 'forms': 'LForm.beqList', 'sb': 'sbBeq', 'nats': 'natListBeq', 'nat': 'Nat.beq'}
TY = {'pre': 'PreludeVal', 'forms': 'List LForm', 'sb': 'List LForm × List (Nat × Nat × Nat)', 'nats': 'List Nat', 'nat': 'Nat'}
deps = {}  # chunk -> file
for gi, g in enumerate(groups):
    body = ''
    for k in g:
        ch = chunks[k]; a, e = ch['start'], ch['end']
        cs = codes[a['ci']:e['ci']]
        body += f'/-- The codes of chunk {k}. -/\ndef codes_{k} : List Nat := unpack {CODE_BASE} {CODE_K} {len(cs)} {wrap(natl(pack(cs, CODE_BASE, CODE_K)))}\n\n'
        o = ch['out']
        if ch['outty'] == 'pre':
            ov = f"(2, 3, 4, 5, 6, 7, 8, 9, 10, {RL}, {NL_}, {SL})"
        elif ch['outty'] == 'forms':
            body += f'/-- The formulas of chunk {k}. -/\ndef out_{k} : List LForm :=\n  {wrap("[" + ", ".join(lf(f) for f in o) + "]")}\n\n'
            ov = f'out_{k}'
        elif ch['outty'] == 'sb':
            body += f'/-- The formulas of chunk {k}. -/\ndef outF_{k} : List LForm :=\n  {wrap("[" + ", ".join(lf(f) for f in o[0]) + "]")}\n\n'
            body += f'/-- The branch histories of chunk {k}. -/\ndef vw_{k} : List (Nat × Nat × Nat) :=\n  {wrap(triplel(o[1]))}\n\n'
            ov = f'(outF_{k}, vw_{k})'
        elif ch['outty'] == 'nats':
            body += f'/-- The result of chunk {k}. -/\ndef out_{k} : List Nat :=\n  {wrap(natl(o))}\n\n'
            ov = f'out_{k}'
        else:
            ov = str(o)
        ch['outval'] = ov
        body += (f'/-- **Chunk {k}** ({ch["kind"]}, nodes {a["len"]}–{e["len"]}), checked by the kernel. -/\n'
                 f'theorem chunk_{k} : chunkOK {BEQ[ch["outty"]]}\n'
                 f'    (({wrap(ch["piece"])}) ((st_{k}).withOracle codes_{k} hubs_{k} lanes_{k}))\n'
                 f'    st_{k + 1} {ov} = true := by\n  decide +kernel\n\n')
        deps[k] = gi
    imports = ['Program', 'Oracle', 'States'] + sorted({f'Chunks{deps[j]}' for k in g for j in range(k) if deps.get(j, gi) != gi and (
        f'out_{j}' in chunks[k]['piece'] or f'outF_{j}' in chunks[k]['piece'] or f'vw_{j}' in chunks[k]['piece'])})
    write(f'Chunks{gi}', f'chunks {g[0]}–{g[-1]}.', body, imports=imports)
print('groups', len(groups))


# ---------------- the assembly proof ----------------
# FM-side terms exactly as the elaborator builds them along the cuts
g5 = [c for c in chunks if c['kind'] == 'items5']
def pairTerm(js):
    i = js[0]['idx']
    if len(js) == 1: return f'(ofLs outF_{i}, vw_{i})'
    rest = pairTerm(js[1:])
    return f'((ofLs outF_{i}, vw_{i}).1 ++ {rest}.1, (ofLs outF_{i}, vw_{i}).2 ++ {rest}.2)'
def ftree(t):
    """The FM term of a formula subtree; items5 leaves are handled by the pair terms."""
    if t[0] == 'leaf':
        i = t[1]
        return f"(ofLs out_{i})"
    if t[0] == 'p5':
        return f'{t[1]}.1'
    return f'({ftree(t[1])} ++ {ftree(t[2])})'
# the items5 subtree as projections of pair terms
def tree5(js):
    if len(js) == 1:
        i = js[0]['idx']
        return ('leaf5', i, f'(ofLs outF_{i}, vw_{i}).1')
    i = js[0]['idx']
    rest = pairTerm(js[1:])
    return ('app5', ('leaf5', i, f'(ofLs outF_{i}, vw_{i}).1'), tree5(js[1:]), f'{rest}.1')
def ftext(t):
    if t[0] == 'leaf': return f'(ofLs out_{t[1]})'
    if t[0] == 'leaf5': return t[2]
    if t[0] == 'app5': return t[3]  # the right-hand part text is stored on the node
    return f'({ftext(t[1])} ++ {ftext(t[2])})'
def leaves2(t):
    if t[0] in ('leaf', 'leaf5'): return [t[1]]
    return leaves2(t[1]) + leaves2(t[2])
by = lambda kind: [ch['idx'] for ch in chunks if ch['kind'] == kind]
def rnest2(xs):
    if len(xs) == 1: return ('leaf', xs[0])
    return ('app', ('leaf', xs[0]), rnest2(xs[1:]))
T5 = tree5(g5)
tree2 = ('app', ('leaf', by('items1')[0]),
         ('app', ('leaf', by('items2')[0]),
          ('app', rnest2(by('items3')),
           ('app', rnest2(by('items4')),
            ('app', ('top5', T5), ('app', ('leaf', by('items6')[0]), ('leaf', by('items7')[0])))))))
def ft(t):
    if t[0] == 'leaf': return f'(ofLs out_{t[1]})'
    if t[0] == 'leaf5': return t[2]
    if t[0] == 'top5': return f'{pairTerm(g5)}.1'
    if t[0] == 'app5':
        return f'({t[1][2]} ++ {t[3]})'
    return f'({ft(t[1])} ++ {ft(t[2])})'

L = []
def cut(k, sim, beq, obtain):
    if k == C - 1:
        L.append(f'  obtain ⟨h1, h2⟩ := cut_end ({sim}) {beq} r chunk_{k}')
        L.append(f'  exact ⟨h1.trans rfl, h2.trans rfl⟩')
        return
    L.append(f'  refine cutS (P := Goal) ({sim}) {beq} r chunk_{k} codes_{k+1} hubs_{k+1} lanes_{k+1}')
    L.append(f'    (hubsAfter_succ hubsData {k} hubs_{k+1} (by decide) hd_{k+1}) (lanesAfter_succ lanesData {k} lanes_{k+1} (by decide) ld_{k+1})')
    L.append(f'    (hd.hubsLim (c := {k+1}) (by decide)) (fun a ha t r => ?_)')
    if obtain: L.append(f'  {obtain}')
OB = {'pre': 'simp only [id] at ha; subst ha', 'forms': 'obtain rfl := map_toL_inj ha',
      'sb': 'obtain rfl := erSB_inj ha', 'nats': 'simp only [id] at ha; subst ha', 'nat': ''}
BS = {'pre': 'preludeBeq_sound', 'forms': 'formsBeq_sound', 'sb': 'sbBeq_sound', 'nats': 'natListBeq_sound\'', 'nat': 'natBeq_sound'}

k = 0
def nextk():
    global k
    ch = chunks[k]; k += 1
    return ch
ch = nextk(); cut(ch['idx'], 'preludeFM_sim2 1399 204', BS['pre'], OB['pre'])
L.append('  unfold NodeCheck.packedFormulasK')
L.append('  rewrite [appendM_seq]')
ch = nextk(); cut(ch['idx'], 'by have := items1_sim2 (Hall := hubsAll hubsData) interpreter (List.range 2) 2 4 5 6 7 8; rwa [interp_map] at this', BS['forms'], OB['forms'])
L.append('  rewrite [appendM_seq]')
ch = nextk(); cut(ch['idx'], f"items2_sim2 2 3 6 7 8 9 10 ({SL})", BS['forms'], OB['forms'])
L.append('  rewrite [appendM_seq]')
g3 = [c for c in chunks if c['kind'] == 'items3']
for j, ch in enumerate(g3):
    nextk()
    s_, n_ = 419 + ch['a'], ch['n']
    if j < len(g3) - 1:
        tot = 1399 - ch['a']
        L.append(f"  rewrite [items3_seq 9 {s_} {n_} {s_ + n_} {tot - n_} {tot} rfl rfl]")
    cut(ch['idx'], f"items3_sim2 9 (List.range' {s_} {n_})", BS['forms'], OB['forms'])
L.append('  rewrite [appendM_seq]')
L.append('  unfold NodeCheck.items4')
L.append("  rewrite [show List.range 204 = List.range' 0 204 from List.range_eq_range']")
g4 = [c for c in chunks if c['kind'] == 'items4']
for j, ch in enumerate(g4):
    nextk()
    a_, n_ = ch['a'], ch['n']
    if j < len(g4) - 1:
        tot = 204 - a_
        L.append(f"  rewrite [seqConcat_seq _ {a_} {n_} {a_ + n_} {tot - n_} {tot} rfl rfl]")
    cut(ch['idx'], f"items4_piece_sim2 6 10 8 9 2 ({RL}) ({NL_}) (List.range' {a_} {n_})", BS['forms'], OB['forms'])
L.append("  rewrite [seq_bind]")
for j, ch in enumerate(g5):
    nextk()
    a_, n_ = ch['a'], ch['n']
    S_a = f"(List.range' {419 + a_} {1399 - a_})"
    if not ch['last']:
        S_b = f"(List.range' {419 + a_ + n_} {1399 - a_ - n_})"
        p = 'interpreter' if a_ == 0 else f'(interpreter.drop {a_})'
        hp = f'(slice_split0 {n_})' if a_ == 0 else f'(slice_split {a_} {n_} {a_ + n_} rfl)'
        L.append(f"  rewrite [subBranchesK_seq 2 ({NL_}) {p} ((interpreter.drop {a_}).take {n_}) (interpreter.drop {a_ + n_}) {a_} {a_ + n_} {S_a} {S_b}")
        L.append(f"    {hp} (by rw [slice_len {a_} {n_} (by norm_num)]) (by rw [slice_len {a_} {n_} (by norm_num), List.drop_range'])]")
        sim = f"by have := subBranchesK_sim2 (Hall := hubsAll hubsData) 2 ({NL_}) {a_} {S_a} ((interpreter.drop {a_}).take {n_}); rwa [slice_map] at this"
    else:
        sim = f"by have := subBranchesK_sim2 (Hall := hubsAll hubsData) 2 ({NL_}) {a_} {S_a} (interpreter.drop {a_}); rwa [drop_map] at this"
    cut(ch['idx'], sim, BS['sb'], OB['sb'])
L.append("  rewrite [appendM_seq, pure_seq, appendM_seq]")
ch = nextk(); cut(ch['idx'], f"by have := items6K_sim2 (Hall := hubsAll hubsData) interpreter 204 (List.range 2) 2 7 ({RL}) ({SL}) ({VW}); rwa [interp_map] at this", BS['forms'], OB['forms'])
ch = nextk(); cut(ch['idx'], f"by have := items7K_sim2 (Hall := hubsAll hubsData) interpreter 2 3 7 ({SL}) ({VW}); rwa [interp_map] at this", BS['forms'], OB['forms'])
L.append("  rewrite [encode_and_seq]")
def enc(t):
    if t[0] == 'leaf':
        ch = nextk(); i = t[1]
        cut(ch['idx'], f"enc_piece_sim2 out_{i}", BS['nats'], OB['nats'])
        return
    if t[0] == 'leaf5':
        ch = nextk(); i = t[1]
        cut(ch['idx'], f"enc_piece_sim2 outF_{i}", BS['nats'], OB['nats'])
        return
    if t[0] == 'top5':
        enc(t[1]); return
    if t[0] == 'app5':
        L.append(f"  rewrite [encodeList_seq]")
        enc(t[1]); enc(t[2]); return
    L.append(f"  rewrite [encodeList_seq]")
    enc(t[1]); enc(t[2])
enc(tree2)
def etree2(t):
    if t[0] in ('leaf', 'leaf5'): return f'out_{enc_of[t[1]]}'
    if t[0] == 'top5': return etree2(t[1])
    return f'({etree2(t[1])} ++ {etree2(t[2])})'
def sq(t):
    if t[0] in ('leaf', 'leaf5'):
        ch = nextk()
        cut(ch['idx'], f"sq_piece_sim2 out_{enc_of[t[1]]}", BS['nats'], OB['nats'])
        return
    if t[0] == 'top5':
        sq(t[1]); return
    L.append(f"  rewrite [squares_seq]")
    sq(t[1]); sq(t[2])
sq(tree2)
ch = nextk(); cut(ch['idx'], f"addL_sim2 {SQ}", BS['nat'], OB['nat'])
assert k == C
imports = ''.join(f'import ZInQKernel.Compiler.NodeSkeleton.Data.Chunks{gi}\n' for gi in range(len(groups)))
final = f'''import ZInQKernel.Compiler.NodeSkeleton.Sim.Assembly
{imports}import ZInQKernel.Compiler.NodeSkeleton.Data.StaticChecks

/-!
# The assembly of the chunks (generated by `gen/gen.py`)

`fast_counts`: the fast run of the packed construction on `𝒰` (`204` registers, `2` inputs)
ends with a node list of `125,307` additions and `98,361` multiplications. The run is cut into
the {C} chunks of `Data/`, each checked by the kernel; `cut` carries the simulation relation from
one pinned state to the next.
-/

set_option linter.constructorNameAsVariable false
set_option simprocs false

namespace ZInQ.Compiler.NodeSkeleton

open Natural NodeCheck Universal

deriving instance DecidableEq for LInstr

theorem interp_map : interpreter.map toLI = interpreterL := by decide +kernel

theorem interp_length : interpreter.length = 1399 := by decide +kernel

theorem slice_len (a n : ℕ) (h : a + n ≤ 1399) : ((interpreter.drop a).take n).length = n := by
  simp only [List.length_take, List.length_drop, interp_length]; omega

theorem slice_split0 (n : ℕ) : interpreter = (interpreter.drop 0).take n ++ interpreter.drop n := by
  rw [List.drop_zero, List.take_append_drop]

theorem slice_split (a n b : ℕ) (h : a + n = b) :
    interpreter.drop a = (interpreter.drop a).take n ++ interpreter.drop b := by
  rw [← h, ← List.drop_drop, List.take_append_drop]

theorem slice_map (a n : ℕ) : ((interpreter.drop a).take n).map toLI = (interpreterL.drop a).take n := by
  rw [List.map_take, List.map_drop, interp_map]

theorem drop_map (a : ℕ) : (interpreter.drop a).map toLI = interpreterL.drop a := by
  rw [List.map_drop, interp_map]

theorem dataOK : DataOK hubsData lanesData limsData :=
  ⟨static_sorted, static_lim, static_first, static_len, fun ℓ hℓ => by
    match ℓ, hℓ with
    | 0, _ => exact static_lane0
    | 1, _ => exact static_lane1
    | 2, _ => exact static_lane2
    | 3, _ => exact static_lane3
    | 4, _ => exact static_lane4⟩

''' + ''.join(f'theorem hd_{j} : hubsData.getD {j} [] = hubs_{j} := by\n  simp only [hubsData, List.getD_cons_succ, List.getD_cons_zero]\n\n' for j in range(C)) + ''.join(f'theorem ld_{j} : lanesData.getD {j} [] = lanes_{j} := by\n  simp only [lanesData, List.getD_cons_succ, List.getD_cons_zero]\n\n' for j in range(C)) + '''/-- The counts of the halting circuit. -/
def Goal (x : ℕ × FState) : Prop :=
  countKind .add x.2.rev = 125307 ∧ countKind .mul x.2.rev = 98361

/-- **The counts of the fast run**, from any state related to the first pinned state (the
state is kept abstract, so that the kernel never runs the fast builder). -/
theorem fast_counts_of (t : FState) (r : Rel (hubsAll hubsData) (hubsAfter hubsData 0)
    (lanesAfter lanesData 0) t ((st_0).withOracle codes_0 hubs_0 lanes_0)) :
    Goal ((NodeCheck.constructionK interpreter 204 2 >>= fun φ => φ.encode) t) := by
  have hd := dataOK
  rewrite [constructionK_seq, interp_length]
''' + '\n'.join(L) + '''

/-- **The counts of the fast run** on the universal interpreter. -/
theorem fast_counts :
    Goal ((NodeCheck.constructionK interpreter 204 2 >>= fun φ => φ.encode) (FState.init 2)) := by
  have r := rel_init dataOK codes_0 (by decide) (by decide)
  rewrite [hd_0, ld_0] at r
  exact fast_counts_of _ r

end ZInQ.Compiler.NodeSkeleton
'''
with open(os.path.join(OUT, 'Final.lean'), 'w') as f:
    f.write(final)
print('final lines', len(final.splitlines()))
