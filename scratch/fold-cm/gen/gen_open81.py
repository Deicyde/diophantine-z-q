"""fold-cm: the CM fold's next generation on fold-c8's top (cm-fold-rebase's gen_open77.py retargeted).

Writes
* ZInQKernel/OneProof/H/CMOpen.lean: the bundles between the new top bundle and the first weak (`_r5`) bundle that carry
  the Gonzalez-Rotger field, copied without it (`_cm`): OpenResearchLeaves60 (TailZ86), 59 (TailZ85), 54SFU
  (D2A6Chain), GR9.OpenResearchLeaves36EBCFSFU, GR9.OpenResearchLeaves35EBCFSFU (D2A6Chain); each conversion a verbatim
  copy with the field's line dropped (59 <- 60, 54SFU <- 59, 36 <- 54SFU, 35 <- 36 (fold-c8's `_hm` copy)); the last is
  the weak-row conversion of OneProof/H/CMR5*.lean (`openResearchLeaves34_of_OpenResearchLeaves35_eb_cf_sf_u_r5`,
  patched: no Gonzalez-Rotger) with its input switched to the `_cm` bundle;
* ZInQKernel/OneProof/H/TailZ<j>.lean: OpenResearchLeaves<m+1> = the head's top research bundle without
  gonzalezRotgerThm512X6RCF and with the five CM-branch inputs, its conversion to OpenResearchLeaves60_cm, and the top
  theorem sixContactMin_of_open<N+1> (numeric names).
Usage: python3 scratch/fold-cm/gen/gen_open81.py   (head: TailZ87 / open80 / OpenResearchLeaves61)
"""
import re, os, sys
sys.path.insert(0, os.path.dirname(__file__))
import leanctx
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../..'))
H = os.path.join(ROOT, 'ZInQKernel/OneProof/H/')
FIELD, FIELD2 = 'gonzalezRotgerThm512X6RCF', 'gonzalezRotgerThm512X6'
TOPK, TOPN, TOPR = 87, 80, 61       # head: TailZ87, sixContactMin_of_open80, OpenResearchLeaves61
NK, NN, NR = TOPK + 1, TOPN + 1, TOPR + 1


def lines(f): return leanctx.lines_of(os.path.join(H, f))


def block(f, start_pat):
    L = lines(f)
    i = [k for k, l in enumerate(L) if re.match(start_pat, l)]
    assert len(i) == 1, (f, start_pat, len(i))
    a = i[0]; b = a + 1
    while b < len(L) and (L[b].startswith(' ') or L[b].strip() == '' and b + 1 < len(L) and L[b + 1].startswith(' ')):
        b += 1
    return L[a:b], a


def drop_field(blk, field):
    out = []; i = 0; hit = 0
    while i < len(blk):
        l = blk[i]
        if re.match(r'^  ' + re.escape(field) + r'\s*(:|:=)', l):
            hit += 1
            while out and (out[-1].startswith('  /--') or (out[-1].startswith('  ') and not re.match(r'^  \w', out[-1]))):
                last = out.pop()
                if last.startswith('  /--'): break
            i += 1
            while i < len(blk) and blk[i].startswith('    '): i += 1
            continue
        out.append(l); i += 1
    assert hit == 1, (blk[0], field, hit)
    return out


def head(blk, old, new, nlines=1):
    s = '\n'.join(blk[:nlines]); assert s.count(old) == 1, (old, s); return s.replace(old, new).split('\n') + blk[nlines:]


def emit(f, a, blk, doc):
    ns, ctx = leanctx.context(os.path.join(H, f), a + 1)
    return '\n'.join([f'-- copied from ZInQKernel/OneProof/H/{f}:{a + 1}, without the Gonzalez-Rotger field', 'section',
                      f'namespace {ns}'] + ctx + [doc] + blk + [f'end {ns}', 'end', ''])


out = []
b, a = block('TailZ86.lean', r'^structure OpenResearchLeaves60 ')
s60 = head(drop_field(b, FIELD), 'structure OpenResearchLeaves60 ', 'structure OpenResearchLeaves60_cm ')
out.append(emit('TailZ86.lean', a, s60, '/-- `OpenResearchLeaves60` without `gonzalezRotgerThm512X6RCF` (fold-cm). -/'))
b, a = block('TailZ85.lean', r'^structure OpenResearchLeaves59 ')
s59 = head(drop_field(b, FIELD), 'structure OpenResearchLeaves59 ', 'structure OpenResearchLeaves59_cm ')
out.append(emit('TailZ85.lean', a, s59, '/-- `OpenResearchLeaves59` without `gonzalezRotgerThm512X6RCF` (fold-cm). -/'))
b, a = block('D2A6Chain.lean', r'^structure OpenResearchLeaves54SFU ')
s54 = head(drop_field(b, FIELD), 'structure OpenResearchLeaves54SFU ', 'structure OpenResearchLeaves54SFU_cm ')
out.append(emit('D2A6Chain.lean', a, s54, '/-- `OpenResearchLeaves54SFU` without `gonzalezRotgerThm512X6RCF` (fold-cm). -/'))
b, a = block('D2A6Chain.lean', r'^structure OpenResearchLeaves36EBCFSFU ')
s36 = head(drop_field(b, FIELD2), 'structure OpenResearchLeaves36EBCFSFU ', 'structure OpenResearchLeaves36EBCFSFU_cm ')
out.append(emit('D2A6Chain.lean', a, s36, '/-- `GR9.OpenResearchLeaves36EBCFSFU` without `gonzalezRotgerThm512X6` (fold-cm). -/'))
b, a = block('D2A6Chain.lean', r'^structure OpenResearchLeaves35EBCFSFU ')
s35 = head(drop_field(b, FIELD2), 'structure OpenResearchLeaves35EBCFSFU ', 'structure OpenResearchLeaves35EBCFSFU_cm ')
out.append(emit('D2A6Chain.lean', a, s35, '/-- `GR9.OpenResearchLeaves35EBCFSFU` without `gonzalezRotgerThm512X6` (fold-cm). -/'))
# conversions
b, a = block('TailZ86.lean', r'^theorem openResearchLeaves59_of_OpenResearchLeaves60 ')
c59 = head(drop_field(b, FIELD), 'theorem openResearchLeaves59_of_OpenResearchLeaves60 (n : OpenResearchLeaves60) : OpenResearchLeaves59 where',
           'theorem openResearchLeaves59_cm_of_60_cm (n : OpenResearchLeaves60_cm) : OpenResearchLeaves59_cm where')
out.append(emit('TailZ86.lean', a, c59, '/-- `openResearchLeaves59_of_OpenResearchLeaves60` without the Gonzalez-Rotger field (fold-cm). -/'))
b, a = block('TailZ85.lean', r'^theorem openResearchLeaves54SFU_of_OpenResearchLeaves59 ')
c54 = head(drop_field(b, FIELD), 'theorem openResearchLeaves54SFU_of_OpenResearchLeaves59 (n : OpenResearchLeaves59) : OpenResearchLeaves54SFU where',
           'theorem openResearchLeaves54SFU_cm_of_59_cm (n : OpenResearchLeaves59_cm) : OpenResearchLeaves54SFU_cm where')
out.append(emit('TailZ85.lean', a, c54, '/-- `openResearchLeaves54SFU_of_OpenResearchLeaves59` without the Gonzalez-Rotger field (fold-cm). -/'))
b, a = block('D2A6Chain.lean', r'^theorem openResearchLeaves36EBCF_of_OpenResearchLeaves53_sf_u ')
c36 = head(drop_field(b, FIELD2), 'theorem openResearchLeaves36EBCF_of_OpenResearchLeaves53_sf_u (n : OpenResearchLeaves54SFU) (t : OpenTextbookLeaves18) : OpenResearchLeaves36EBCFSFU where',
           'theorem openResearchLeaves36EBCFSFU_cm_of_54SFU_cm (n : _root_.HDec.HSyn.OpenResearchLeaves54SFU_cm) (t : OpenTextbookLeaves18) : OpenResearchLeaves36EBCFSFU_cm where')
out.append(emit('D2A6Chain.lean', a, c36, '/-- `GR9.openResearchLeaves36EBCF_of_OpenResearchLeaves53_sf_u` without the Gonzalez-Rotger field (fold-cm). -/'))
b, a = block('C8Chain.lean', r'^theorem openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf_sf_u_hm ')
c35 = drop_field(b, FIELD2)
c35 = head(c35, 'theorem openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf_sf_u_hm (n : OpenResearchLeaves36EBCFSFU)',
           'theorem openResearchLeaves35EBCFSFU_cm_of_36_cm (n : OpenResearchLeaves36EBCFSFU_cm)', 1)
c35 = head(c35, ': OpenResearchLeaves35EBCFSFU where', ': OpenResearchLeaves35EBCFSFU_cm where', 2)
out.append(emit('C8Chain.lean', a, c35, '/-- fold-c8\'s `openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf_sf_u_hm` without the Gonzalez-Rotger field (fold-cm). -/'))
# the weak conversion 35 -> 34 (CMR5, patched: reads no Gonzalez-Rotger field)
for f in ('CMR5_1.lean', 'CMR5_2.lean', 'CMR5.lean'):
    if any(l.startswith('theorem _root_.HDec.HSyn.GR9.openResearchLeaves34_of_OpenResearchLeaves35_eb_cf_sf_u_r5 ') for l in lines(f)):
        b, a = block(f, r'^theorem _root_\.HDec\.HSyn\.GR9\.openResearchLeaves34_of_OpenResearchLeaves35_eb_cf_sf_u_r5 '); src = f
c34 = head(b, 'theorem _root_.HDec.HSyn.GR9.openResearchLeaves34_of_OpenResearchLeaves35_eb_cf_sf_u_r5 (n : OpenResearchLeaves35EBCFSFU)',
           'theorem _root_.HDec.HSyn.GR9.openResearchLeaves34_r5_of_35EBCFSFU_cm (n : _root_.HDec.HSyn.GR9.OpenResearchLeaves35EBCFSFU_cm)')
assert not any(FIELD2 + ' ' in l or FIELD2 + '\n' in l for l in c34 if 'n.' + FIELD2 in l), 'weak conversion still reads the field'
out.append(emit(src, a, c34, '/-- The weak-row conversion (`OneProof/H/CMR5*.lean`, patched: `gonzalezRotgerX6Ab` from `x6CoarseModuli`) on the `_cm` bundle (fold-cm). -/'))

hdr = '''import ZInQKernel.OneProof.H.CMR5

/-! # fold-cm: the bundles that carry the Gonzalez-Rotger field, without it (generated by `scratch/fold-cm/gen/gen_open81.py`)

On the CM-branch route (`OneProof/H/CMR5*.lean`) no theorem reads `gonzalezRotgerThm512X6RCF` /
`gonzalezRotgerThm512X6`: its only readers were the producers of `R5ptProps` and of `gonzalezRotgerX6Ab`, replaced by the
weak row (cm-branch2) and by `QMSplit.Moduli.gonzalezRotgerX6Ab_r5_of_coarse`. The bundles from fold-c8's research
generation down to the weak conversion are copied here without the field (`_cm`), each conversion verbatim with the field's
line dropped. The originals are unchanged. -/

set_option maxHeartbeats 1000000
set_option linter.style.longLine false
noncomputable section

'''
open(H + 'CMOpen.lean', 'w').write(hdr + '\n'.join(out) + '\nend\n')

CM_FIELDS = [
    '  /-- cm-branch (GLUE, open): A8 at a CM fibre and the matrix units (diophantine_zq.tex L520-562, L581-586). -/',
    '  cmFibreSplit : _root_.HDec.CMBranch.CMFibreSplit',
    '  /-- cm-branch (leaf, printed form, pending review): Fowler, Math. Proc. Cambridge Philos. Soc. 180 (2026), Prop. 2.7 (L588-590). -/',
    '  fowlerProp27 : _root_.HDec.CMBranch.FowlerProp27',
    '  /-- cm-branch (leaf, ELLIOT-literature, pending review): the degree of a singular modulus, #Pic(R) <= [L:Q] (L586-587). -/',
    '  cmjDegree : _root_.HDec.CMBranch.CMjDegree',
    '  /-- cm-branch (leaf, ELLIOT-literature, pending review): CM elliptic curves have potentially good reduction (L596-597). -/',
    '  cmPotentialGood : _root_.HDec.CMBranch.CMPotentialGood',
    '  /-- cm-branch (leaf, consequence form, pending review): Barquero-Sanchez et al., Res. Number Theory 3 (2017), Eq. (6.2) (L600-605). -/',
    '  cmHeight62 : _root_.HDec.CMBranch.CMHeight62']
b, a = block(f'TailZ{TOPK}.lean', rf'^structure OpenResearchLeaves{TOPR} ')
sN = drop_field(b, FIELD)
sN = [f'/-- `OpenResearchLeaves{TOPR}` without `gonzalezRotgerThm512X6RCF` (read by no theorem of the CM-branch route) and with the',
      'five CM-branch inputs (`CMBranch.CMInputs3`; fold-cm, the CM-branch package: the manuscript\'s CM branch, L581-631). -/',
      f'structure OpenResearchLeaves{NR} : Prop where'] + sN[1:] + CM_FIELDS
b, a = block(f'TailZ{TOPK}.lean', rf'^theorem openResearchLeaves60_of_OpenResearchLeaves{TOPR} ')
cN = head(drop_field(b, FIELD), f'theorem openResearchLeaves60_of_OpenResearchLeaves{TOPR} (n : OpenResearchLeaves{TOPR}) (l : OpenAddedLeaves28) : OpenResearchLeaves60 where',
          f'theorem openResearchLeaves60_cm_of_OpenResearchLeaves{NR} (n : OpenResearchLeaves{NR}) (l : OpenAddedLeaves28) : OpenResearchLeaves60_cm where')
tail = f'''import ZInQKernel.OneProof.H.CMOpen

/-! # OneProof H, fold-cm: `sixContactMin_of_open{NN}` (the CM-branch package; generated by scratch/fold-cm/gen/gen_open81.py)

Jack's ruling (to "Should [the CM-branch package] fold now?"): "Fold now at +4 (Recommended)".
Field removed: `gonzalezRotgerThm512X6RCF` (research; read by no theorem of the CM-branch route). Fields added:
`cmFibreSplit` (GLUE), `fowlerProp27`, `cmjDegree`, `cmPotentialGood`, `cmHeight62` (leaves pending review). The route:
fold-c8's chain with its base (FS5 / NoCM) replaced by the manuscript's CM branch (diophantine_zq.tex L581-631;
`Contrib/OneProof/CMBranchUC8.lean`, `OneProof/H/CMTopLive.lean`), the moduli row carried in its weak form (`R5ptProps`
as `True`, `OneProof/H/CMR5*.lean`) and the bundles without the field (`OneProof/H/CMOpen.lean`). `CoxProperLattice`,
`ReducedCMPeriod` and `HeightAdditivityUpper` are proved. -/

namespace HDec

namespace HSyn

''' + '\n'.join(sN) + '\n\n' + '/-- `OpenResearchLeaves60_cm` from the new generation (fold-c8\'s conversion without the Gonzalez-Rotger field). -/\n' + '\n'.join(cN) + f'''

/-- **G0 with only the open leaves and the open glue** (fold-cm, the CM-branch package): the manuscript's CM branch
(L581-631) in place of NoCM; González–Rotger's Thm 5.12 no longer read. -/
theorem sixContactMin_of_open{NN} (r : OpenResearchLeaves{NR}) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves28) : ZInQ.SixContactMin :=
  let t16 := openTextbookLeaves16_of_OpenTextbookLeaves17 (openTextbookLeaves17_of_OpenTextbookLeaves18 t)
  _root_.HDec.HSyn.GR9.sixContactMin_of_open45_pz_eb_sf_u_hm_cm_r5
    (c := ⟨r.cmFibreSplit, r.fowlerProp27, r.cmjDegree, r.cmPotentialGood, r.cmHeight62⟩)
    (_root_.HDec.HSyn.GR9.openResearchLeaves31_of_OpenResearchLeaves32_eb_cf_sf_u_r5
      (_root_.HDec.HSyn.GR9.openResearchLeaves32_of_OpenResearchLeaves33_eb_cf_sf_u_r5
        (_root_.HDec.HSyn.GR9.openResearchLeaves33_of_OpenResearchLeaves34_eb_cf_sf_u_r5
          (_root_.HDec.HSyn.GR9.openResearchLeaves34_r5_of_35EBCFSFU_cm
            (GR9.openResearchLeaves35EBCFSFU_cm_of_36_cm
              (GR9.openResearchLeaves36EBCFSFU_cm_of_54SFU_cm
                (openResearchLeaves54SFU_cm_of_59_cm (openResearchLeaves59_cm_of_60_cm
                  (openResearchLeaves60_cm_of_OpenResearchLeaves{NR} r l))) t)
              (_root_.DeRhamScholze.HTMerge.hodgeTateDecompAbVar_of_scholzeH1 l.scholzeH1AbVar l.t10TateDuality)) t16) t16)))
    t16 _root_.ZInQ.Contrib.CloudR2Poincare.poincareComplement_proof
    (_root_.HDec.G0Galois.C8Conrad.c8Inputs_of_leaves (c8Leaves_of_OpenAddedLeaves28 l))

end HSyn

end HDec

#print axioms HDec.HSyn.sixContactMin_of_open{NN}
'''
open(H + f'TailZ{NK}.lean', 'w').write(tail)
print('wrote CMOpen.lean, TailZ%d.lean' % NK)
