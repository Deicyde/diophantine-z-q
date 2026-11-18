"""fold-c8: the joint C8 fold (C8 by local algebraicity, Poincaré from PR #86, Hodge-Tate from Scholze), regenerated
on the current top. Count-neutral: the Picard rows (picRepresentableAbVar, kleimanPicZeroProper954SiteQ) and the
research row hodgeTateDecompOr leave; conradAppB, scholzeH1AbVar, t10TateDuality enter (all GLUE).

Run from the repository root, after building Main and the component modules and running the taint:

    lake env lean scratch/fold-c8/gen/Taint.lean > scratch/fold-c8/gen/taint_out.txt
    python3 scratch/fold-c8/fold_c8.py [--dry-run]

It writes
* `ZInQKernel/OneProof/H/C8Chain.lean`: c8-conrad2's generated copy (scratch/fold-c8/gen/gen.py on the taint list:
  every declaration of frozenTarget's proof that reads `t09SymmIsogenyExists`, `phiAmpleIsogeny`,
  `weilPairingMumford`, `detTate` or takes a bundle carrying one, renamed `_c8`/`C8`, the C8 reader replaced by
  `C8Conrad.g12DetPZ_of_inputs`), then a top section generated here from the live declarations: consumer (iii)
  (`openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf*` with `hodgeTateDecompAbVar` from
  `DeRhamScholze.HTMerge.hodgeTateDecompAbVar_of_scholzeH1`), consumer (ii) (`openTextbookLeaves13HF_of_open16_P`
  with Poincaré) and copies of the top theorems down to the swap point, each `_hm`;
* `ZInQKernel/OneProof/H/TailZ<j>.lean` (first free number): the research bundle without `hodgeTateDecompOr`, the
  added bundle without the Picard rows with the three new leaves, the conversion (filling `hodgeTateDecompOr` from
  the Scholze leaf and Milne, `hodgeTateDecompOr_of_scholzeH1Milne`; the rerouted chain does not read it), and the
  next top `sixContactMin_of_open<N+1>` with `poincareComplement` from PR #86's `poincareComplement_proof`;
* Main.lean switched (import, binders, call, one paragraph); kinds.tsv rows replaced. claims.tsv is not touched.
"""
import csv, os, re, subprocess, sys

ROOT = os.getcwd()
sys.path.insert(0, os.path.join(ROOT, 'scripts/one_proof'))
sys.path.insert(0, os.path.join(ROOT, 'scratch/fold-c8/gen'))
import autofold as af  # noqa: E402  (main_state, find_struct, field_groups, bump, flag_class, counts)
import render_open  # noqa: E402
from copylib import emit, find_decl  # noqa: E402

DRY = '--dry-run' in sys.argv
G = 'scratch/fold-c8/gen'
H = 'ZInQKernel/OneProof/H/'
CHAIN = H + 'C8Chain.lean'
C8T = '_root_.HDec.G0Galois.C8Conrad.C8Inputs'
HPT = '_root_.ZInQ.Contrib.AVB1.PoincareComplement'
HNT = '_root_.DeRhamScholze.HTMerge.ScholzeH1AbVar'
HTT = '_root_.T10Etale.T10_TateDuality'
PIC = ('picRepresentableAbVar', 'kleimanPicZeroProper954SiteQ')
HTOR = 'hodgeTateDecompOr'


def die(m):
    print('fold_c8: ' + m)
    sys.exit(1)


SEEN_TOP = set()


def decl_text(name, kinds=('theorem',)):
    """(file, text with context) of the unique declaration `name` (short name) under OneProof/H."""
    hits = []
    for fn in sorted(os.listdir(H)):
        f = H + fn
        if f == CHAIN or not f.endswith('.lean'):
            continue
        for i in find_decl(f, name, kinds):
            hits.append((f, i))
    if len(hits) != 1:
        die(f'{name}: {len(hits)} declarations under {H}')
    f, _ = hits[0]
    return f, emit(f, name, {}, (), kinds, 0, SEEN_TOP)


def sub1(txt, a, b, what):
    if txt.count(a) != 1:
        die(f'{what}: expected one occurrence of {a!r}, found {txt.count(a)}')
    return txt.replace(a, b)


main_src, binders, top, N, last_mod, k = af.main_state()
bvar = dict(binders)
R, T, A = bvar['r'], bvar['t'], bvar['l']
print(f'current top {top} ({last_mod}): r : {R}, t : {T}, l : {A}')
if T != 'OpenTextbookLeaves18':
    die(f'textbook bundle {T}: this fold expects the empty OpenTextbookLeaves18')
_, ablock = af.find_struct(A)
afields = [f for f, _ in af.field_groups(ablock)]
if sorted(afields) != sorted(PIC):
    die(f'added bundle {A} has fields {afields}; this fold expects exactly the Picard rows {PIC}')
_, rblock = af.find_struct(R)
rgroups = af.field_groups(rblock)
if HTOR not in [f for f, _ in rgroups]:
    die(f'research bundle {R} has no field {HTOR}')

# ---- the chain of top theorems from the current top down to open79 (research-only autofolds above it) ----
passes = []  # (k, research bundle at k, conversion name) for k = N .. 80
kk = N
while kk > 79:
    pat = re.compile(r'^theorem sixContactMin_of_open' + str(kk) + r' \(r : (\w+)\) \(t : OpenTextbookLeaves18\) '
                     r'\(l : OpenAddedLeaves27\) : ZInQ\.SixContactMin :=\n  sixContactMin_of_open' + str(kk - 1)
                     + r' \((\w+) r\) t l$', re.M)
    m = None
    for fn in sorted(os.listdir(H)):
        if fn.endswith('.lean') and H + fn != CHAIN:
            m = m or pat.search(open(H + fn).read())
    if not m:
        die(f'sixContactMin_of_open{kk} is not a research-only autofold top; extend the generator')
    passes.append((kk, m.group(1), m.group(2)))
    kk -= 1
_, t79 = decl_text('sixContactMin_of_open79')
m79 = re.search(r'theorem sixContactMin_of_open79 \(r : (\w+)\) \(t : OpenTextbookLeaves18\) \(l : OpenAddedLeaves27\)'
                r' : ZInQ\.SixContactMin :=\n  sixContactMin_of_open78 \((\w+) r\) t l', t79)
_, t78 = decl_text('sixContactMin_of_open78')
m78 = re.search(r'theorem sixContactMin_of_open78 \(r : (\w+)\) \(t : OpenTextbookLeaves18\) \(l : OpenAddedLeaves27\) :\s*'
                r'ZInQ\.SixContactMin :=\n  sixContactMin_of_open73_sf_u \((\w+) r\) t l', t78)
_, t73 = decl_text('sixContactMin_of_open73_sf_u')
if not (m79 and m78 and 'GR9.sixContactMin_of_open72_sf_u r t l' in t73):
    die('the chain open79 -> open78 -> open73_sf_u -> GR9.open72_sf_u changed; regenerate the top section by hand')

# ---- 1. generated copy (c8-conrad2's generator) ----
taint = G + '/taint_out.txt'
if not os.path.exists(taint):
    die(f'run the taint first: lake env lean {G}/Taint.lean > {taint}')
body = G + '/chain_body.lean.txt'
# the top theorems from the swap point up are replaced by the edited copies of the top section
EXCL = ['sixContactMin_of_open45_pz_eb_sf_u', 'sixContactMin_of_open48_eb_k954_sf_u', 'sixContactMin_of_open72_sf_u',
        'sixContactMin_of_open73_sf_u', 'sixContactMin_of_open78', 'sixContactMin_of_open79'] + \
       [f'sixContactMin_of_open{kk}' for kk, _, _ in passes]
out = subprocess.run([sys.executable, G + '/gen.py', taint, body, ','.join(EXCL), G + '/header.lean'],
                     capture_output=True, text=True)
print(out.stdout[-3000:], out.stderr[-3000:])
if out.returncode != 0:
    die('gen.py failed')
gen = open(body).read()
# top-level context lines already emitted by the generated part (emitted once; repeated top-level `open`s can make
# names ambiguous, piczero-char0)
SEEN_TOP = {l for l in gen.split('\n') if re.match(r'^(open|set_option|attribute|universe|variable) ', l)}

# ---- 2. top section: copies with the three swaps ----
def gen_block(name):
    m = re.search(r'(-- copied from [^\n]*\(' + re.escape(name) + r'\)\n.*?)(?=\n-- copied from |\Z)', gen, re.S)
    if not m:
        die(f'generated copy has no block {name}')
    return m.group(1)

top_sec = ['', '/-! ## Top section (fold-c8, generated by scratch/fold-c8/fold_c8.py from the live declarations)', '',
           'Consumer (iii): `hodgeTateDecompAbVar` from `DeRhamScholze.HTMerge.hodgeTateDecompAbVar_of_scholzeH1` (the',
           'Scholze leaf and Milne\'s identification); consumer (ii): Poincaré complete reducibility as an argument',
           '(`openTextbookLeaves13HF_of_open16_P`); consumer (i): the generated copy above with `c8`. No declaration',
           'below takes the Picard rows. -/', '']

# (iii)
_, t35 = decl_text('openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf_sf_u')
m35 = re.search(r'theorem (openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf_sf_u) \(n : (\w+)\) '
                r'\(t : OpenTextbookLeaves16\) \(l : OpenAddedLeaves26\) : (\w+) where', t35)
if not m35:
    die('consumer (iii) signature changed')
t35 = t35.replace(m35.group(0), f'theorem {m35.group(1)}_hm (n : {m35.group(2)})\n    (hHT : _root_.ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar) : {m35.group(3)} where')
t35 = sub1(t35, '  hodgeTateDecompAbVar := hodgeTateDecompAbVar_of_open_k954 n.hodgeTateDecompExists t.mumfordTorsionAlgClosed l.picRepresentableAbVar l.kleimanPicZeroProper954\n',
           '  hodgeTateDecompAbVar := hHT\n', 'consumer (iii)')
if re.search(r'(?<![\w.])[tl]\.', t35.split(' where', 1)[1]):
    die('consumer (iii) copy still reads t or l')
t35 = re.sub(r'/--.*?-/\n', '/-- Copy of `' + m35.group(1) + '` (D2A6Chain) with `hodgeTateDecompAbVar` read from `hHT` (consumer\n(iii) off the Picard rows); every other field verbatim; `t`, `l` dropped (unread). -/\n', t35, count=1, flags=re.S)
top_sec.append(t35.replace('-- copied from', '-- edited copy of', 1))

# openAddedLeaves18 without t, l
b18 = gen_block('openAddedLeaves18_of_OpenAddedLeaves22_pz')
m18 = re.search(r'theorem openAddedLeaves18_of_OpenAddedLeaves22_pz_c8 \(c8 : [\w.]+\) \(t : (\w+)\) \(n : OpenAddedLeaves22PZ\) :\s+(\w+) where', b18)
if not m18:
    die('openAddedLeaves18_of_OpenAddedLeaves22_pz_c8 signature not as expected')
b18 = b18.replace(m18.group(0), f'theorem openAddedLeaves18_hm (c8 : {C8T}) : {m18.group(2)} where')
if re.search(r'(?<![\w.])[tn]\.', b18.split(' where', 1)[1]):
    die('openAddedLeaves18 copy reads t or n')
b18 = re.sub(r'/--.*?-/\n', '/-- Copy of the generated `openAddedLeaves18_of_OpenAddedLeaves22_pz_c8` without its unread arguments `t`, `n`\n(`n : OpenAddedLeaves22PZ` carries the Picard rows). -/\n', b18, count=1, flags=re.S)
top_sec.append(b18.replace('-- copied from', '-- edited copy of', 1))

# (ii): open45
_, t45 = decl_text('sixContactMin_of_open45_pz_eb_sf_u')
t45 = sub1(t45, '(r : OpenResearchLeaves31EBSFU) (t : OpenTextbookLeaves16) (l : OpenAddedLeaves22PZ) :',
           f'(r : OpenResearchLeaves31EBSFU) (t : OpenTextbookLeaves16)\n    (hP : {HPT}) (c8 : {C8T}) :', 'open45 binders')
t45 = sub1(t45, 'theorem sixContactMin_of_open45_pz_eb_sf_u ', 'theorem sixContactMin_of_open45_pz_eb_sf_u_hm ', 'open45 name')
t45 = sub1(t45, '  sixContactMin_of_open37_hf_gm_pz_eb_sf_u\n', '  sixContactMin_of_open37_hf_gm_pz_eb_sf_u_c8\n', 'open45 callee')
t45 = sub1(t45, '(openTextbookLeaves13HF_of_open16_22_pz t r.neronSchemeExtensionDedekind l)',
           '(openTextbookLeaves13HF_of_open16_P t r.neronSchemeExtensionDedekind hP)', 'open45 (ii)')
t45 = sub1(t45, '(openAddedLeaves18_of_OpenAddedLeaves22_pz t l)', '(openAddedLeaves18_hm c8)', 'open45 (i)')
t45 = re.sub(r'/--.*?-/\n', '/-- Copy of `sixContactMin_of_open45_pz_eb_sf_u` (D2A6Chain): Poincaré from `hP` (consumer (ii)), the added\nbundle replaced by the C8 inputs `c8` (consumer (i)). -/\n', t45, count=1, flags=re.S)
if 'theorem sixContactMin_of_open37_hf_gm_pz_eb_sf_u_c8 ' not in gen:
    die('generated copy lacks sixContactMin_of_open37_hf_gm_pz_eb_sf_u_c8')
top_sec.append(t45.replace('-- copied from', '-- edited copy of', 1))

# open72_sf_u with (iii) and without l26 / open48
_, t72 = decl_text('sixContactMin_of_open72_sf_u')
t72 = sub1(t72, 'theorem sixContactMin_of_open72_sf_u (r : OpenResearchLeaves54SFU) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves27) : ZInQ.SixContactMin :=',
           f'theorem sixContactMin_of_open72_sf_u_hm (r : OpenResearchLeaves54SFU) (t : OpenTextbookLeaves18)\n    (hP : {HPT}) (c8 : {C8T})\n    (hN : {HNT}) (hT : {HTT}) : ZInQ.SixContactMin :=', 'open72 sig')
t72 = sub1(t72, '  let l26 := openAddedLeaves26_of_OpenAddedLeaves27 l\n', '', 'open72 l26')
t72 = sub1(t72, 'sixContactMin_of_open48_eb_k954_sf_u (', 'sixContactMin_of_open45_pz_eb_sf_u_hm (', 'open72 callee')
t72 = sub1(t72, '(openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf_sf_u (openResearchLeaves36EBCF_of_OpenResearchLeaves53_sf_u r t) t16 l26)',
           '(openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf_sf_u_hm (openResearchLeaves36EBCF_of_OpenResearchLeaves53_sf_u r t) (_root_.DeRhamScholze.HTMerge.hodgeTateDecompAbVar_of_scholzeH1 hN hT))', 'open72 (iii)')
t72 = sub1(t72, ' t16 l26\n', ' t16 hP c8\n', 'open72 tail')
t72 = re.sub(r'/--.*?-/\n', '/-- Copy of `sixContactMin_of_open72_sf_u` (D2A6Chain) with the three swaps; `sixContactMin_of_open48_eb_k954_sf_u`\n(which only converts the Picard bundle) bypassed. No added bundle. -/\n', t72, count=1, flags=re.S)
top_sec.append(t72.replace('-- copied from', '-- edited copy of', 1))

SW = f'(hP : {HPT}) (c8 : {C8T})\n    (hN : {HNT}) (hT : {HTT})'
top_sec += ['namespace HDec', 'namespace HSyn', '',
            '/-- Copy of `sixContactMin_of_open73_sf_u`, `sixContactMin_of_open78` and `sixContactMin_of_open79` with the three swaps. -/',
            f'theorem sixContactMin_of_open79_hm (r : {m79.group(1)}) (t : OpenTextbookLeaves18)\n    {SW} : ZInQ.SixContactMin :=',
            f'  GR9.sixContactMin_of_open72_sf_u_hm ({m78.group(2)} ({m79.group(2)} r)) t hP c8 hN hT', '']
for kk, rb, conv in reversed(passes):
    top_sec += [f'/-- Copy of `sixContactMin_of_open{kk}` with the three swaps. -/',
                f'theorem sixContactMin_of_open{kk}_hm (r : {rb}) (t : OpenTextbookLeaves18)\n    {SW} : ZInQ.SixContactMin :=',
                f'  sixContactMin_of_open{kk - 1}_hm ({conv} r) t hP c8 hN hT', '']
top_sec += ['end HSyn', 'end HDec', '', f'#print axioms HDec.HSyn.sixContactMin_of_open{N}_hm', '']

hdr = open(G + '/chain_header.lean').read().replace('{TOPMOD}', last_mod)
chain_txt = hdr + gen[len(open(G + '/header.lean').read()):] + '\n'.join(top_sec)

# ---- 3. TailZ<j>: bundles and top ----
Rn, An = af.bump(R), af.bump(A)
j = k + 1
while os.path.exists(f'{H}TailZ{j}.lean'):
    j += 1
new_mod = f'TailZ{j}'
LEAVES = [
    ('conradAppB', '_root_.HDec.G0Galois.C8Conrad.ConradAppB',
     'Conrad, Lifting global representations with local properties (author preprint, Dec. 11 2011), App. B, p. 32 '
     '(Hodge-Tate => locally algebraic, `ConradAppBQp`) and p. 33 Prop. B.3 (the Hodge-Tate weight is the exponent, '
     '`ConradPropB3Qp`), base field `ℚ_p`: the manuscript\'s citation at diophantine_zq.tex L760-762 (step C8). '
     'Replaces the Picard route to `DetTate` (consumer (i)).'),
    ('scholzeH1AbVar', HNT,
     'Scholze, p-adic Hodge theory for rigid-analytic varieties, Forum Math. Pi 1 (2013), Cor. 1.8 with Thms 9.1, 9.3 '
     '(diophantine_zq.tex lem:de-rham-descent L10954-10965, step C3) with the Hodge numbers of `H¹_dR(A/F)` (L10996): '
     '`H¹_et(A_F̄, ℚ_p)` of an abelian variety of dimension g over a finite `F/ℚ_p` is de Rham with Hodge jumps in '
     '[0, 1] and `dim Fil¹ D_dR = [F:ℚ_p] g`, over Mathlib\'s pro-étale `Scheme.EllAdicCohomology`. General g is a '
     'generalization (the manuscript\'s lemma is g = 2, `ScholzeH1AbSurf`, implied).'),
    ('t10TateDuality', HTT,
     'Milne, Abelian varieties v2.00, Part I, Thm 12.1(a), as the manuscript cites it (lem:de-rham-descent '
     'L10966-10970); Milne 1986 (Cornell-Silverman) Thm 15.1(a): `H¹(A_K̄, ℤ_ℓ) = Hom(T_ℓ A, ℤ_ℓ)`, '
     'Galois-equivariantly, over Mathlib\'s pro-étale `EllAdicCohomology`.'),
]
tz = [f'import ZInQKernel.OneProof.H.C8Chain', 'import ZInQKernel.Contrib.CloudR2Poincare.FinalUnconditional', '',
      f'/-! # OneProof H, fold-c8: `sixContactMin_of_open{N + 1}` (the joint C8 fold; generated by scratch/fold-c8/fold_c8.py)',
      '',
      'Fields removed: `picRepresentableAbVar`, `kleimanPicZeroProper954SiteQ` (added) and `hodgeTateDecompOr` (research;',
      'no longer read: filled in the conversion from the Scholze leaf and Milne). Fields added: `conradAppB`,',
      '`scholzeH1AbVar`, `t10TateDuality` (added). `poincareComplement` is proved',
      '(`ZInQ.Contrib.CloudR2Poincare.poincareComplement_proof`). -/', '', 'namespace HDec', '', 'namespace HSyn', '',
      f'/-- `{R}` without `{HTOR}` (fold-c8: its only reader, consumer (iii), now takes the Scholze leaf). -/',
      f'structure {Rn} : Prop where']
for f, lines in rgroups:
    if f != HTOR:
        tz.extend(lines)
tz += ['', f'/-- `{A}` without the Picard rows, with the leaves of the joint C8 fold (all GLUE until reviewed). -/',
       f'structure {An} : Prop where']
for nm, ty, doc in LEAVES:
    tz += [f'  /-- {doc} -/', f'  {nm} : {ty}']
convR = f'{R[0].lower()}{R[1:]}_of_{Rn}'
tz += ['', f'/-- `{R}` from `{Rn}`: `{HTOR}` from the Scholze leaf and Milne\'s identification',
       '(`DeRhamScholze.HTMerge.hodgeTateDecompOr_of_scholzeH1Milne`); the rerouted chain does not read it. -/',
       f'theorem {convR} (n : {Rn}) (l : {An}) : {R} where']
for f, _ in rgroups:
    tz.append(f'  {f} := _root_.DeRhamScholze.HTMerge.hodgeTateDecompOr_of_scholzeH1Milne l.scholzeH1AbVar l.t10TateDuality'
              if f == HTOR else f'  {f} := n.{f}')
tz += ['', f'/-- The C8 leaves of `{An}` (`C8Conrad.C8Leaves` = Conrad App. B). -/',
       f'theorem c8Leaves_of_{An} (n : {An}) : _root_.HDec.G0Galois.C8Conrad.C8Leaves where',
       '  conradAppB := n.conradAppB', '',
       f'/-- **G0 with only the open leaves and the open glue** (fold-c8, the joint C8 fold): C8 by local algebraicity',
       '(Conrad App. B), Poincaré proved (PR #86), `hodgeTateDecompAbVar` from Scholze and Milne; no Picard row. -/',
       f'theorem sixContactMin_of_open{N + 1} (r : {Rn}) (t : OpenTextbookLeaves18) (l : {An}) : ZInQ.SixContactMin :=',
       f'  sixContactMin_of_open{N}_hm ({convR} r l) t _root_.ZInQ.Contrib.CloudR2Poincare.poincareComplement_proof',
       f'    (_root_.HDec.G0Galois.C8Conrad.c8Inputs_of_leaves (c8Leaves_of_{An} l)) l.scholzeH1AbVar l.t10TateDuality',
       '', 'end HSyn', '', 'end HDec', '', f'#print axioms HDec.HSyn.sixContactMin_of_open{N + 1}', '']

# ---- 4. Main.lean ----
ms = main_src.replace(f'import ZInQKernel.OneProof.H.{last_mod}', f'import ZInQKernel.OneProof.H.{new_mod}', 1)
ms = sub1(ms, f'(r : HDec.HSyn.{R})', f'(r : HDec.HSyn.{Rn})', 'Main r')
ms = sub1(ms, f'(l : HDec.HSyn.{A})', f'(l : HDec.HSyn.{An})', 'Main l')
ms = sub1(ms, f'(HDec.HSyn.{top} r t l)', f'(HDec.HSyn.sixContactMin_of_open{N + 1} r t l)', 'Main call')
PARA = (f'The joint C8 fold (fold-c8: c8-conrad3, conrad-b3, ht-merge with derham-scholze and ht-abvar, and PR #86) removed the\n'
        f'added fields `picRepresentableAbVar` and `kleimanPicZeroProper954SiteQ` and the research field `hodgeTateDecompOr`,\n'
        f'and added `conradAppB` (Conrad App. B p. 32 and Prop. B.3, the manuscript\'s citation at L760-762),\n'
        f'`scholzeH1AbVar` (Scholze 2013 with the Hodge numbers of `H¹`, lem:de-rham-descent) and `t10TateDuality` (Milne):\n'
        f'step C8 now follows the manuscript (`C8Conrad.g12DetPZ_of_inputs`, `Contrib/OneProof/C8*.lean`), Poincaré\'s\n'
        f'complete reducibility is proved (`ZInQ.Contrib.CloudR2Poincare.poincareComplement_proof`), and\n'
        f'`hodgeTateDecompAbVar` comes from Scholze and Milne (`DeRhamScholze.HTMerge.hodgeTateDecompAbVar_of_scholzeH1`).\n'
        f'`{Rn}` and `{An}` (`{new_mod}`) are the new generations, and `HDec.HSyn.sixContactMin_of_open{N + 1}` goes through\n'
        f'`sixContactMin_of_open{N}_hm`, a copy of the chain of declarations that read the Weil-pairing fields of step C8\n'
        f'(`OneProof/H/C8Chain.lean`, generated by `scratch/fold-c8/fold_c8.py`; copy reroute); no existing declaration\n'
        f'is changed.\n\n')
ms = sub1(ms, 'The hypotheses of `frozenTarget` are therefore exactly the open statements.',
          PARA + 'The hypotheses of `frozenTarget` are therefore exactly the open statements.', 'Main paragraph')

# ---- 5. kinds.tsv ----
SPEC_FLAGS = {
    'conradAppB': dict(
        kind='consequence',
        flag=('pending review (new merged leaf, GLUE until a reviewer rates it); page read by the reading desk 11-17; '
              'unrefereed preprint, the manuscript\'s own citation. Part p. 32 (ConradAppBQp, unchanged): the reviewer\'s '
              'strict leaf review GLUE/GLUE, consequence with unproved bridges (HasHTWeights{w} => print-HT; Q_p-homs '
              'G_m -> R_{E/Q_p}G_m are x -> x^n). Part Prop. B.3 (ConradPropB3Qp): consequence, Conrad\'s conventions '
              '(arithmetic Artin map = Tau Ceti\'s; chi_cyc weight +1); bridge from the print\'s decomposition C_p (x) V = '
              'sum V_sigma, V_sigma = C_p(w_sigma), w_sigma = n, to dim_Qp H_n = [E:Q_p] is linear algebra plus '
              'Ax-Sen-Tate over Q_p (proved in the tree, CloudB3W11.axSenTate_proof), not formalized. On the spot in '
              'step C8 (proved glue, not a row): TwistCharHTWt0 (the twisting character is Hodge-Tate of weight 0 at 5, '
              'L758-760)'),
        source=('Conrad, Lifting global representations with local properties, author preprint Dec. 11 2011, App. B: '
                'p. 32 (arithmetic normalization, HT <=> locally algebraic paragraph after Def. B.1) and p. 33 Prop. B.3 '
                '(proof pp. 33-34), base field Q_p; diophantine_zq.tex L760-762, bibitem L11046-11049')),
    'scholzeH1AbVar': dict(
        kind='consequence',
        flag=('pending review: new leaf (merges scholzeDeRhamAlg, used only for abelian varieties in degree 1, and '
              'hodgeNumberH1AbVar), consequence: rigid-analytic spaces and H^1_dR are not in Mathlib, so Cor. 1.8 and the '
              'Hodge numbers are stated on the etale side of the filtered comparison (dictionary steps: analytification + '
              'Thms 9.1/9.3 in the manuscript; Fbar vs C_p; Mathlib\'s pro-etale l-adic cohomology vs classical etale '
              'cohomology, on the spot); generalization (on the spot) in g: the manuscript\'s lemma is for abelian surfaces '
              '(g = 2, ScholzeH1AbSurf, stated and implied); general g is needed because the H field hodgeTateDecompAbVar '
              '(TailS L347) and R10 (ZInQ.Contrib.R10.DeRhamComparisonHT) are stated for every g, although their only end '
              'consumer (G9, g9GlueNoT23_of_fieldEmb) uses g = 2; h^{1,0}(A) = g (Mumford, Abelian varieties, section 4) '
              'locator UNVERIFIED; journal numbering of Scholze UNVERIFIED here (locators.md R10)'),
        source=('diophantine_zq.tex lem:de-rham-descent L10939-10965 and L10996 (Scholze, Forum Math. Pi 1 (2013), Cor. 1.8, '
                'Thms 9.1, 9.3, corrigendum Forum Math. Pi 4 (2016) e6; Hodge numbers 2,2 of H^1_dR(A/F)); general g: '
                'h^{1,0}(A) = g, Mumford, Abelian varieties, section 4 (UNVERIFIED)')),
    't10TateDuality': dict(
        kind='published',
        flag=('unread: the leaf T10Etale.T10_TateDuality reused unchanged (an earlier review: leaf, confirmed); '
              'Milne v2.00 Part I Thm 12.1(a) and Milne 1986 Thm 15.1(a) not read; equivariance from canonicity '
              'and the pro-etale/etale comparison (Bhatt-Scholze 2015 section 5.6) are dictionary steps; locator UNVERIFIED'),
        source=('Milne, Abelian varieties v2.00 Part I Thm 12.1(a) (manuscript\'s citation, L10966-10970) / Milne 1986 '
                'Thm 15.1(a): V_l(A) = H^1_et(A_Kbar, Q_l)^dual, Galois-equivariantly, over Mathlib\'s pro-etale l-adic '
                'cohomology (T10Etale.T10_TateDuality)')),
}
rows, cols = af.load_kinds()
before = af.counts(rows)
gone = set(PIC) | {HTOR}
if not gone <= {r['field'] for r in rows}:
    die('kinds.tsv lacks one of ' + str(gone))
LIKE = {'conradAppB': 'picRepresentableAbVar', 'scholzeH1AbVar': HTOR, 't10TateDuality': HTOR}  # packet/label/tier/area
kept = [r for r in rows if r['field'] not in gone]
new_rows = []
for nm, d in SPEC_FLAGS.items():
    like = next(r for r in rows if r['field'] == LIKE[nm])
    strict = 'LEAF' if d['kind'] == 'published' and not render_open.must_be_glue(d['flag']) else 'GLUE'
    strictest = 'GLUE' if d['flag'].startswith('strictest') else strict
    new_rows.append(dict(bundle='added', field=nm, kind=d['kind'], flag=d['flag'], strict=strict, strictest=strictest,
                         source=d['source'], rated_by='fold-c8 (joint C8 fold); pending review',
                         packet=like.get('packet', ''), label=like.get('label', ''), tier=like.get('tier', ''),
                         flag_class=af.flag_class(d['flag'], strict, strictest), area_issue=like.get('area_issue', '')))
kept += new_rows
with open(af.CLAIMS, newline='') as fh:
    held = {r['field'] for r in csv.DictReader(fh, delimiter='\t') if r.get('hold') == 'held'}
problems = [p for r in new_rows for p in render_open.kinds_row_problems(r, {r['field'] for r in kept}, held)]
if problems:
    die('new kinds rows fail render_open checks: ' + '; '.join(problems))
after = af.counts(kept)
print(f'strict count: {before[1]}/{before[2]} on {before[0]} -> {after[1]}/{after[2]} on {after[0]}; '
      f'strictest {before[3]}/{before[4]} -> {after[3]}/{after[4]}')
if after[2] > before[2] or after[4] > before[4]:
    die('a GLUE count rises; not folding')
if DRY:
    open(G + '/C8Chain-dryrun.lean.txt', 'w').write(chain_txt)
    open(G + f'/{new_mod}-dryrun.lean.txt', 'w').write('\n'.join(tz))
    print(f'dry run: wrote {G}/C8Chain-dryrun.lean.txt and {G}/{new_mod}-dryrun.lean.txt only')
    sys.exit(0)
open(CHAIN, 'w').write(chain_txt)
open(f'{H}{new_mod}.lean', 'w').write('\n'.join(tz))
open(af.MAIN, 'w').write(ms)
order = {'research': 0, 'textbook': 1, 'added': 2, 'glue': 3}
pos = {r['field']: i for i, r in enumerate(rows)}
kept.sort(key=lambda r: (order.get(r['bundle'], 9), r['field'].lower() if r['bundle'] in order else pos.get(r['field'], 0)))
with open(af.KINDS, 'w', newline='') as fh:
    w = csv.DictWriter(fh, fieldnames=cols, delimiter='\t', lineterminator='\n', extrasaction='ignore')
    w.writeheader()
    w.writerows(kept)
print(f'wrote {CHAIN}, {H}{new_mod}.lean (sixContactMin_of_open{N + 1}, {Rn}, {An}), switched Main.lean, kinds.tsv')
