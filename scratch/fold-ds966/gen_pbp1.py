"""fold-ds966, fold 2 (pb-p1): replace the research fields panPrintedP and bergerPrintedVT (bergerPrintedV in the
generations before pb-pst's TailZ72) by pb-p1's leaves panPrintedF and bergerSurveyF over Fontaine's B_st.

`PanDict.panBerger_of_F` proves `r11r12 : PanBerger` from the two new leaves (and the DS fields), but the new Pan
leaf does not give the old field panPrintedP (that would need B_max[log p~]-pst => Fontaine-pst, which pb-p1 records
as the non-leaf BmaxStToFontaine). So the fold is a copy reroute (pattern of fold33-copy / pb-p1's gen_bypass.py):

* ZInQKernel/OneProof/H/PanFontaineCopy.lean, namespace HDec.HSyn.PBP1: a copy of every research generation from
  OpenResearchLeaves40 (the first with panPrintedP, TailZ65) to the current top generation K (read from Main.lean)
  with the two fields replaced, a copy of their conversion maps (the TailZ65 map fills r11r12 by
  panBerger_of_F; the TailZ72 map's `bergerPrintedV := bergerPrintedV_of_T n.bergerPrintedVT` becomes
  `bergerSurveyF := n.bergerSurveyF`; every other line is copied verbatim), and a verbatim copy of every top theorem
  `sixContactMin_of_open*` of OneProof/H/ whose signature takes one of these generations. Inside the namespace, name
  resolution picks the copies; the generation 39 and everything older are the originals. No existing declaration
  changes.
* ZInQKernel/OneProof/H/TailZ<j+1>.lean (autofold's shape, so later autofolds parse it): OpenResearchLeaves<K+1>
  (the generation K copy's fields), its field-by-field map to PBP1.OpenResearchLeaves<K>, and the next top theorem
  sixContactMin_of_open<N+1>.
* Main.lean switched to it.

Run from the repository root on any head whose research generations >= 40 still carry panPrintedP (this asserts
every edit and stops otherwise):
    python3 scratch/fold-ds966/gen_pbp1.py
Then update kinds.tsv / reviews.tsv with scratch/fold-ds966/rows_pbp1.py and run the checks.
"""
import glob, re, sys

H = 'ZInQKernel/OneProof/H/'
MAIN = 'ZInQKernel/OneProof/Main.lean'
NL = '\n'
FIRST = 40

PAN_T = '_root_.HDec.PkgI4.PanDict.PanPrintedP'
BERV_T = '_root_.HDec.PkgI4.PanDict.BergerPrintedV'
BERVT_T = '_root_.HDec.PkgI4.PanDict.BergerPrintedVT'
PAN_DOC = ('  /-- R12 (pb-p1). Pan, J. Amer. Math. Soc. 35 (2022), Theorem 1.0.4 (= arXiv:1901.07166v2 Thm 1.0.4 p. 5 with '
           'Conj. 1.0.1 p. 2), p >= 5, printed form with "potentially semi-stable in the sense of Fontaine" over '
           "Fontaine's B_st = B_cris[log p~] inside B_dR (Berger, arXiv:math/0210184v1, II.3.1 and II.3.3), basis form, "
           "on a model V = E^n; otherwise as pb-fix3's PanPrintedP. -/")
BER_DOC = ("  /-- R11 (pb-p1). Berger's theorem (Invent. Math. 148 (2002) Thm 0.7) in the printed form of Berger, An "
           'introduction to the theory of p-adic representations (arXiv:math/0210184v1, IV.5.1 p. 30, IV.5.3 p. 31): '
           "a de Rham p-adic representation V = E^n of G_Qp is potentially semistable over Fontaine's "
           'B_st = B_cris[log p~] (II.3.1, II.3.3), basis form (I.2.3). -/')
PAN_NEW = '  panPrintedF : _root_.HDec.PkgI4.PanDict.PanPrintedF'
BER_NEW = '  bergerSurveyF : _root_.HDec.PkgI4.PanDict.BergerSurveyF'


def die(m):
    sys.exit('gen_pbp1: ' + m)


def lines(fn):
    return open(fn).read().split(NL)


def tail_num(fn):
    m = re.search(r'TailZ(\d+)\.lean$', fn)
    return int(m.group(1)) if m else -1


def find_decl(prefix):
    """(file, start, end) of the unique top-level declaration whose first line starts with prefix, among H/*.lean."""
    hits = []
    for fn in sorted(glob.glob(H + '*.lean')):
        L = lines(fn)
        for i, l in enumerate(L):
            if l.startswith(prefix):
                hits.append((fn, i))
    if len(hits) != 1:
        die(f'{len(hits)} declarations start with {prefix!r}: {hits}')
    fn, i = hits[0]
    L = lines(fn)
    j = i + 1
    if prefix.startswith('structure'):
        while j < len(L) and L[j].strip() != '' and not L[j].startswith(('theorem', 'def', 'structure', 'end', '/-')):
            j += 1
    else:
        while j < len(L) and L[j].strip() != '':
            j += 1
    return fn, L[i:j]


def swap_field(B, old_t, doc, new, what):
    hits = [i for i, l in enumerate(B) if re.match(r'^  \w+ : ' + re.escape(old_t) + r'$', l.rstrip())]
    if len(hits) != 1:
        die(f'{what}: {len(hits)} fields of type {old_t}')
    i = hits[0]
    k = i
    if B[i - 1].rstrip().endswith('-/'):
        k = i - 1
        while not B[k].lstrip().startswith('/--'):
            k -= 1
    return B[:k] + [doc, new] + B[i + 1:]


def swap_map(B, what):
    out, n = [], 0
    for l in B:
        r = l.rstrip()
        if r == '  panPrintedP := n.panPrintedP':
            out.append('  panPrintedF := n.panPrintedF'); n += 1
        elif r in ('  bergerPrintedV := n.bergerPrintedV', '  bergerPrintedVT := n.bergerPrintedVT',
                   '  bergerPrintedV := _root_.HDec.PkgI4.PanDict.bergerPrintedV_of_T n.bergerPrintedVT'):
            out.append('  bergerSurveyF := n.bergerSurveyF'); n += 1
        elif r.startswith('  r11r12 := _root_.HDec.PkgI4.PanDict.panBerger_of_printedPV n.panPrintedP n.bergerPrintedV '):
            out.append(l.replace('panBerger_of_printedPV n.panPrintedP n.bergerPrintedV',
                                 'panBerger_of_F n.panPrintedF n.bergerSurveyF')); n += 10
        else:
            if re.search(r'panPrintedP|bergerPrintedV', l):
                die(f'{what}: unexpected use: {l}')
            out.append(l)
    return out, n


main = open(MAIN).read()
mr = re.search(r'\(r : HDec\.HSyn\.OpenResearchLeaves(\d+)\)', main)
mt = re.search(r'\(t : HDec\.HSyn\.(OpenTextbookLeaves\d+)\)', main)
ml = re.search(r'\(l : HDec\.HSyn\.(OpenAddedLeaves\d+)\)', main)
mtop = re.search(r'\(HDec\.HSyn\.sixContactMin_of_open(\d+) r t l\)', main)
mimp = re.search(r'^import ZInQKernel\.OneProof\.H\.TailZ(\d+)$', main, re.M)
if not (mr and mt and ml and mtop and mimp):
    die('cannot parse Main.lean')
K, T, L_, N, J = int(mr.group(1)), mt.group(1), ml.group(1), int(mtop.group(1)), int(mimp.group(1))
if K < FIRST:
    die(f'top research generation {K} < {FIRST}')

out = []
P = out.append
P(f'import ZInQKernel.OneProof.H.TailZ{J}')
P('import ZInQKernel.Contrib.OneProof.PanBergerFontaine')
P('')
P('/-! # OneProof H, fold-ds966 (pb-p1): research generations with Pan and Berger over Fontaine\'s `B_st`')
P('')
P('Generated by scratch/fold-ds966/gen_pbp1.py (copy reroute; pattern of fold33-copy and pb-p1\'s gen_bypass.py).')
P(f'The namespace `HDec.HSyn.PBP1` copies the research generations `OpenResearchLeaves{FIRST}`-`{K}` with the fields')
P('`panPrintedP` (Pan, JAMS 2022 Thm 1.0.4, pst over Berger\'s `B_max[log p~]`) and `bergerPrintedV`/`bergerPrintedVT`')
P('(Berger 2002 Thm 0.7) replaced by pb-p1\'s leaves `panPrintedF` and `bergerSurveyF` (both over Fontaine\'s')
P('`B_st = B_cris[log p~]` as Berger\'s survey prints it), copies their conversion maps (the generation-40 map fills')
P('`r11r12` by `PanDict.panBerger_of_F`, with no comparison of period rings; every other line verbatim), and copies')
P('verbatim every top theorem `sixContactMin_of_open*` that takes one of these generations. Inside the namespace,')
P('name resolution picks the copies; generation 39 and older, and every original, are unchanged.')
P('-/')
P('')
P('namespace HDec')
P('')
P('namespace HSyn')
P('')
P('namespace PBP1')
P('')
total = 0
nmaps = 0
gens = list(range(FIRST, K + 1))
topfile = None
for k in gens:
    fn, S = find_decl(f'structure OpenResearchLeaves{k} : Prop where')
    pan = PAN_T
    ber = BERVT_T if any(re.search(re.escape(BERVT_T) + r'$', l) for l in S) else BERV_T
    S = swap_field(S, pan, PAN_DOC, PAN_NEW, f'gen {k} pan')
    S = swap_field(S, ber, BER_DOC, BER_NEW, f'gen {k} berger')
    P(f'/-- fold-ds966 (pb-p1) copy of `HDec.HSyn.OpenResearchLeaves{k}` with `panPrintedP` and the Berger field '
      'replaced by `panPrintedF`, `bergerSurveyF`. -/')
    out.extend(S)
    P('')
    _, M = find_decl(f'theorem openResearchLeaves{k - 1}_of_OpenResearchLeaves{k} ')
    M, n = swap_map(M, f'map {k}')
    total += n
    nmaps += 1
    P(f'/-- fold-ds966 (pb-p1) copy of `HDec.HSyn.openResearchLeaves{k - 1}_of_OpenResearchLeaves{k}`'
      + (f' (target: the original generation {FIRST - 1}; `r11r12` by `PanDict.panBerger_of_F`).' if k == FIRST else '.')
      + ' -/')
    out.extend(M)
    P('')
    if k == K:
        topfile = fn
if total != 10 + 2 * len(gens):
    die(f'unexpected number of map edits: {total} (expected {10 + 2 * len(gens)})')

# top theorems taking a copied generation, in chain order (TailZ number, then line)
genpat = re.compile(r'\(r : OpenResearchLeaves(\d+)\)')
tops = []
for fn in glob.glob(H + '*.lean'):
    Ls = lines(fn)
    for i, l in enumerate(Ls):
        m = re.match(r'^theorem (sixContactMin_of_open\w*) ', l)
        if m:
            g = genpat.search(l)
            if g and int(g.group(1)) >= FIRST:
                j = i + 1
                while j < len(Ls) and Ls[j].strip() != '':
                    j += 1
                tops.append((tail_num(fn), i, m.group(1), Ls[i:j], fn))
tops.sort()
names = [t[2] for t in tops]
if len(set(names)) != len(names):
    die(f'duplicate top theorem names: {names}')
if f'sixContactMin_of_open{N}' not in names:
    die(f'the current top sixContactMin_of_open{N} is not among the copied tops {names}')
for tn, i, name, B, fn in tops:
    if any(re.search(r'panPrintedP|bergerPrintedV', l) for l in B):
        die(f'top theorem {name} reads a replaced field')
    P(f'/-- fold-ds966 (pb-p1) copy of `HDec.HSyn.{name}` ({fn.split("/")[-1]}). -/')
    out.extend(B)
    P('')
P('end PBP1')
P('')
P('end HSyn')
P('')
P('end HDec')
P('')
P(f'#print axioms HDec.HSyn.PBP1.sixContactMin_of_open{N}')
open(H + 'PanFontaineCopy.lean', 'w').write(NL.join(out) + NL)

# the new top module
_, S = find_decl(f'structure OpenResearchLeaves{K} : Prop where')
ber = BERVT_T if any(re.search(re.escape(BERVT_T) + r'$', l) for l in S) else BERV_T
S = swap_field(S, PAN_T, PAN_DOC, PAN_NEW, 'top pan')
S = swap_field(S, ber, BER_DOC, BER_NEW, 'top berger')
body = S[1:]
fields = [m.group(1) for l in body for m in [re.match(r'^  ([A-Za-z_][\w\']*) :', l)] if m and not l.lstrip().startswith('/--')]
conv = [f'  {f} := n.{f}' for f in fields]
J2, K2, N2 = J + 1, K + 1, N + 1
top = f'''import ZInQKernel.OneProof.H.TailZ{J}
import ZInQKernel.OneProof.H.PanFontaineCopy

/-! # OneProof H, fold-ds966 (pb-p1): `sixContactMin_of_open{N2}` (written by scratch/fold-ds966/gen_pbp1.py after autofold's pattern)

Fields removed: `panPrintedP`, `bergerPrintedVT`.
Fields added (new leaves): `panPrintedF` (Pan arXiv:1901.07166v2 Thm 1.0.4 over Fontaine's `B_st`), `bergerSurveyF`
(Berger, arXiv:math/0210184v1 IV.5.1 over Fontaine's `B_st`; = Berger 2002 Thm 0.7). Readers rerouted by the copy
`ZInQKernel/OneProof/H/PanFontaineCopy.lean` (`r11r12 := PanDict.panBerger_of_F`); no existing declaration changed. -/

namespace HDec

namespace HSyn

/-- `OpenResearchLeaves{K}` without `panPrintedP`, `bergerPrintedVT`, with the leaves `panPrintedF`, `bergerSurveyF` (fold-ds966, pb-p1). -/
structure OpenResearchLeaves{K2} : Prop where
{NL.join(body)}

/-- `PBP1.OpenResearchLeaves{K}` (fold-ds966's copy of `OpenResearchLeaves{K}` with Pan and Berger over Fontaine's `B_st`) from `OpenResearchLeaves{K2}`, field by field. -/
theorem openResearchLeaves{K}PBP1_of_OpenResearchLeaves{K2} (n : OpenResearchLeaves{K2}) : PBP1.OpenResearchLeaves{K} where
{NL.join(conv)}

/-- **G0 with only the open leaves and the open glue** (fold-ds966, pb-p1; generated). -/
theorem sixContactMin_of_open{N2} (r : OpenResearchLeaves{K2}) (t : {T}) (l : {L_}) : ZInQ.SixContactMin :=
  PBP1.sixContactMin_of_open{N} (openResearchLeaves{K}PBP1_of_OpenResearchLeaves{K2} r) t l

end HSyn

end HDec

#print axioms HDec.HSyn.sixContactMin_of_open{N2}
'''
open(H + f'TailZ{J2}.lean', 'w').write(top)

subs = [(f'import ZInQKernel.OneProof.H.TailZ{J}\n', f'import ZInQKernel.OneProof.H.TailZ{J2}\n'),
        (f'(r : HDec.HSyn.OpenResearchLeaves{K})', f'(r : HDec.HSyn.OpenResearchLeaves{K2})'),
        (f'(HDec.HSyn.sixContactMin_of_open{N} r t l)', f'(HDec.HSyn.sixContactMin_of_open{N2} r t l)')]
for old, new in subs:
    if main.count(old) != 1:
        die('Main: ' + old)
    main = main.replace(old, new)
open(MAIN, 'w').write(main)
print(f'PanFontaineCopy.lean ({len(gens)} generations {FIRST}..{K}, {nmaps} maps, {len(tops)} top theorems: '
      f'{", ".join(names)}); TailZ{J2}.lean (OpenResearchLeaves{K2}, sixContactMin_of_open{N2}); Main patched')
