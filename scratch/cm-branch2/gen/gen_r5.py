"""cm-branch2: generate the R5ptProps prune copies (weak-row bypass).

Input: scratch/cm-branch2/dirty.tsv (output of scratch/cm-branch2/Dirty.lean): name, module, idx, range, TYPE|value.
Every non-generated dirty declaration is copied verbatim from its source file, in import/line order, into
ZInQKernel/Contrib/OneProof/CMBranch/R5Prune.lean, in its own namespace and context, with
  * every reference to a dirty declaration renamed `<last>_r5` (same namespace),
  * every `R5ptProps a b` replaced by `True` (the weak row: the conjunct carried but never read),
  * hand patches (PATCHES below) at the producers that built R5ptProps from González–Rotger.
"""
import re, sys, os
sys.path.insert(0, os.path.dirname(__file__))
import leanctx

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../..'))
GEN_SUFFIXES = ('.mk', '.rec', '.recOn', '.casesOn', '.noConfusion', '.noConfusionType', '.ctorIdx',
                '.sizeOf_spec', '.injEq', '.inj', '.mk.injEq', '.mk.inj', '.mk.sizeOf_spec', '.mk.noConfusion',
                '.ext', '.ext_iff', '.congr_simp')
SKIP = {'HDec.HSyn.r5fp_of_rep', 'ShimuraSplit.r5fp_of_point', 'ShimuraSplit.point_of_r5fp',
        'GRDict.r5ptProps_of_thm512', 'GRDict.gonzalezRotgerX6Ab_of_witness',
        'GRX6AbPrint.gonzalezRotgerX6Ab_of_coarse', 'GRX6AbPrint.gonzalezRotgerX6Ab_of_print'}
SEEDS = {'LeafQM.AV.R5ptProps', 'HDec.HSyn.OpenResearchLeaves53.gonzalezRotgerThm512X6RCF'}

rows = []
for line in open(os.path.join(ROOT, 'scratch/cm-branch2/dirty.tsv')):
    parts = line.rstrip('\n').split('\t')
    if len(parts) < 5: continue
    name, mod, idx, rng, kind = parts[:5]
    rows.append((name, mod, int(idx), rng, kind))

structs = set()
# structures: their projections are generated; detect by a `.mk` sibling in the list
names = {r[0] for r in rows}
for n in names:
    if n.endswith('.mk'):
        structs.add(n[:-3])

srange = {}
for (name, mod, idx, rng, kind) in rows:
    if name in structs and rng != '-':
        a, b = map(int, rng.split('-'))
        srange[name] = (mod, a, b)
rowmap = {r[0]: r for r in rows}
def generated(n):
    if n in SEEDS or n in SKIP: return True
    if any(n.endswith(s) for s in GEN_SUFFIXES): return True
    if re.search(r'\._proof_\d+$|\.match_\d+|\._simp_\d+|\.eq_\d+$|\._sunfold$|\._unsafe_rec$|_def$', n): return True
    for s in structs:
        if n.startswith(s + '.') and n.count('.') == s.count('.') + 1:
            r = rowmap.get(n)
            if s in srange and r is not None and r[3] != '-':
                a = int(r[3].split('-')[0])
                m, sa, sb = srange[s]
                if not (r[1] == m and sa <= a <= sb):
                    return False   # a theorem in the structure's namespace (dot notation), not a field
            return True   # projection
    return False

copies = [r for r in rows if not generated(r[0]) and r[3] != '-']
# the structures themselves (their `.mk` is dirty)
for (name, mod, idx, rng, kind) in rows:
    if name.endswith('.mk') and name[:-3] in structs:
        S = name[:-3]
        path = os.path.join(ROOT, mod.replace('.', '/') + '.lean')
        L = leanctx.lines_of(path)
        last = S.split('.')[-1]
        hits = [i for i, l in enumerate(L) if re.match(r'^structure\s+' + re.escape(last) + r'\b', l)]
        if len(hits) != 1:
            print('STRUCT?', S, len(hits)); continue
        a = hits[0]
        # include docstring above
        s0 = a
        if s0 > 0 and L[s0 - 1].rstrip().endswith('-/'):
            while s0 > 0 and not L[s0 - 1].startswith('/--'):
                s0 -= 1
            s0 -= 1
        b = a + 1
        while b < len(L) and (L[b].startswith(' ') or L[b].strip() == '' and b + 1 < len(L) and L[b + 1].startswith(' ')):
            b += 1
        if not any(c[0] == S for c in copies):
            copies.append((S, mod, idx, f'{s0 + 1}-{b}', 'TYPE'))
copies.sort(key=lambda r: (r[2], int(r[3].split('-')[0])))
rename = {r[0] for r in copies}
dstructs = {r[0] for r in copies if r[0] in structs}
def newname(full):
    c = full.split('.')
    for k in range(1, len(c)):
        if '.'.join(c[:k]) in dstructs:
            return '.'.join(c[:k - 1] + [c[k - 1] + '_r5'] + c[k:])
    return '.'.join(c[:-1] + [c[-1] + '_r5'])
by_last = {}
for n in rename:
    by_last.setdefault(n.split('.')[-1], []).append(n.split('.'))

TOK = re.compile(r"(?<![\w'.!?])((?:_root_\.)?[^\W\d][\w'!?]*(?:\.[\w'!?]+)*)")

def ren_token(m):
    t = m.group(1)
    root = t.startswith('_root_.')
    comps = (t[len('_root_.'):] if root else t).split('.')
    # find the longest prefix of comps that is a suffix (component-wise) of a dirty name, whose last is dirty
    for k in range(len(comps), 0, -1):
        head = comps[:k]
        cands = by_last.get(head[-1], [])
        for c in cands:
            if k == 1 and any('.'.join(c[:j]) in dstructs for j in range(1, len(c))):
                continue   # S.x members are only referenced qualified or by dot notation
            if (root and c == head) or (not root and c[-k:] == head):
                return '_root_.' + '.'.join([newname('.'.join(c))] + comps[k:])
    return t

R5RE = re.compile(r"(?:_root_\.)?(?:LeafQM\.AV\.)?R5ptProps\s+(\([^()]*\)|[^\s()]+)\s+(\([^()]*\)|[^\s()]+)")

def transform(text):
    text = R5RE.sub('True', text)
    return TOK.sub(ren_token, text)

def main():
    out = ['import ZInQKernel.Contrib.OneProof.CMBranch.Top2', '',
           '/-! # cm-branch2: the weak-row bypass (R5ptProps carried as `True`), generated by',
           '`scratch/cm-branch2/gen/gen_r5.py` from the dirty set `scratch/cm-branch2/dirty.tsv`. Every declaration is a',
           'verbatim copy of the named original with dirty references renamed `_r5` and `R5ptProps X Ψ` replaced by `True`',
           '(hand patches listed in the generator). -/', '', 'set_option maxHeartbeats 1000000', 'set_option autoImplicit false', '']
    for name, mod, idx, rng, kind in copies:
        path = os.path.join(ROOT, mod.replace('.', '/') + '.lean')
        a, b = map(int, rng.split('-'))
        ns, ctx = leanctx.context(path, a)
        blk = leanctx.block(path, a, b)
        if 'SGRDirect' in mod:
            blk = re.sub(r"(?<![\w.\[])X(?![\w'\]])(?!\s*:=)", 'Polynomial.X', blk)
        out.append(f'-- copied from {mod} {a}-{b} ({name}, {kind})')
        out.append('noncomputable section')
        if ns: out.append(f'namespace {ns}')
        out.extend(ctx)
        out.append(transform(blk))
        if ns: out.append(f'end {ns}')
        out.append('end')
        out.append('')
        if name == 'HDec.QMSplit.Moduli.GonzalezRotgerX6Ab':
            out.append(HELPER)
    txt = '\n'.join(out)
    for pat, rep in PATCHES:
        if pat not in txt:
            print('PATCH NOT FOUND:', pat[:80]); continue
        txt = txt.replace(pat, rep)  # all occurrences
    # split into parts under ~140 KB at block boundaries ("-- copied from" lines)
    head_end = txt.index('-- copied from')
    header, rest = txt[:head_end], txt[head_end:]
    blocks = ['-- copied from' + b for b in rest.split('-- copied from')[1:]]
    parts, cur = [], ''
    for b in blocks:
        if len((cur + b).encode()) > 140000 and cur:
            parts.append(cur); cur = ''
        cur += b
    parts.append(cur)
    n = len(parts)
    names = [f'R5Prune{i + 1}' for i in range(n - 1)] + ['R5Prune']
    base = os.path.join(ROOT, 'ZInQKernel/Contrib/OneProof/CMBranch/')
    for i, (nm, body) in enumerate(zip(names, parts)):
        imp = 'import ZInQKernel.Contrib.OneProof.CMBranch.Top2' if i == 0 else f'import ZInQKernel.Contrib.OneProof.CMBranch.{names[i - 1]}'
        h = header.replace('import ZInQKernel.Contrib.OneProof.CMBranch.Top2', imp)
        h = h.replace('-/', f'Part {i + 1} of {n}. -/', 1)
        open(base + nm + '.lean', 'w').write(h + body)
    print('parts:', names)
    print(len(copies), 'copies,', len(txt.splitlines()), 'lines')

HELPER = """
-- cm-branch2 (hand-written): the weak `gonzalezRotgerX6Ab` without González–Rotger
noncomputable section
namespace HDec.QMSplit.Moduli
open LeafQM LeafQM.AV
/-- **The weak field `gonzalezRotgerX6Ab` (`R5ptProps` carried as `True`) from the coarse leaf `X6CoarseModuli` and
the research field `shimuraMainThmIDeligneY3AbU`, without González–Rotger's Thm 5.12**: the witness is
`GRX6AbPrint.x6ModuliWitness_of_coarse` (proved; it does not use Thm 5.12). -/
theorem gonzalezRotgerX6Ab_r5_of_coarse (hY : RayClassCFT.ShimuraMainThmIDeligneY3AbU)
    (hX : _root_.GRX6AbPrint.X6CoarseModuli) : _root_.HDec.QMSplit.Moduli.GonzalezRotgerX6Ab_r5 := by
  obtain ⟨Y, Φ, X, Ψ, fY, h1, h6⟩ := _root_.GRX6AbPrint.x6ModuliWitness_of_coarse hY hX
  exact ⟨Y, Φ, X, Ψ, fY, h1, h6, trivial⟩
end HDec.QMSplit.Moduli
end
"""

PATCHES = [
 ("(h : LeafQM.AV.R5fp) : _root_.HDec.QMSplit.Moduli.ResidueOfX6_r5 :=\n  fun _ _ _ _ _ _ h6 => ShimuraSplit.point_of_r5fp h h6",
  ": _root_.HDec.QMSplit.Moduli.ResidueOfX6_r5 :=\n  fun _ _ _ _ _ _ _ => trivial"),
 ("(hR : LeafQM.AV.R1rec)\n    (h5 : LeafQM.AV.R5fp) : _root_.HDec.LeafAdopt.R1R2fpRepW_r5 :=",
  "(hR : LeafQM.AV.R1rec) :\n    _root_.HDec.LeafAdopt.R1R2fpRepW_r5 :="),
 ("(_root_.HDec.QMSplit.Moduli.residueOfX6_of_r5fp_r5 h5)", "_root_.HDec.QMSplit.Moduli.residueOfX6_of_r5fp_r5"),
 ("    (hR : LeafQM.AV.R1rec) (h5 : LeafQM.AV.R5fp) : _root_.HDec.LeafAdopt.R1R2fpRepW_r5 :=\n  _root_.HDec.QMSplit.Moduli.r1r2fpRep_of_splitW_r5 (canonicalCoarseX6_ofW hG hL) hB hR h5",
  "    (hR : LeafQM.AV.R1rec) : _root_.HDec.LeafAdopt.R1R2fpRepW_r5 :=\n  _root_.HDec.QMSplit.Moduli.r1r2fpRep_of_splitW_r5 (canonicalCoarseX6_ofW hG hL) hB hR"),
 ("    (hR : LeafQM.AV.R1rec) (h5 : LeafQM.AV.R5fp) : _root_.HDec.LeafAdopt.R1R2fpRepW_r5 :=\n  _root_.HDec.QMSplit.Moduli.r1r2fpRep_of_split5W_r5 hG hL (babaGranathX6_of hB) hR h5",
  "    (hR : LeafQM.AV.R1rec) : _root_.HDec.LeafAdopt.R1R2fpRepW_r5 :=\n  _root_.HDec.QMSplit.Moduli.r1r2fpRep_of_split5W_r5 hG hL (babaGranathX6_of hB) hR"),
 ("  refine _root_.HDec.QMSplit.Moduli.r1r2fpRep_of_split6W_r5 (_root_.HDec.QMSplit.Moduli.geomConnX6W_of_gr_r5 hG) hL hB (r1rec_of_reciprocityCanonical hR) ?_\n  obtain ⟨Y, Φ, X, Ψ, fY, -, h6, h5⟩ := hG\n  exact ShimuraSplit.r5fp_of_point ⟨Y, Φ, X, Ψ, fY, h6, h5⟩",
  "  exact _root_.HDec.QMSplit.Moduli.r1r2fpRep_of_split6W_r5 (_root_.HDec.QMSplit.Moduli.geomConnX6W_of_gr_r5 hG) hL hB (r1rec_of_reciprocityCanonical hR)"),
 ("  r5 : LeafQM.AV.R5fp\n", "  r5 : True\n"),
 ("  r5 := r5fp_of_rep r.r1r2", "  r5 := trivial"),
 ("gonzalezRotgerX6Ab := _root_.GRX6AbPrint.gonzalezRotgerX6Ab_of_print n.gonzalezRotgerThm512X6 n.shimuraMainThmIDeligneY3AbU n.x6CoarseModuli t.gagaMorphism t.mumfordTorsionAlgClosed",
  "gonzalezRotgerX6Ab := _root_.HDec.QMSplit.Moduli.gonzalezRotgerX6Ab_r5_of_coarse n.shimuraMainThmIDeligneY3AbU n.x6CoarseModuli"),
]

if __name__ == '__main__':
    main()
