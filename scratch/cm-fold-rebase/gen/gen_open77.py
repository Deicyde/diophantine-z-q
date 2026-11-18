"""cm-fold-rebase: the fold's next generation on main's top (ZInQKernel/Contrib/OneProof/CMFoldRebase/Open77.lean).

cm-branch2's gen_open73.py moved to open76 (TailZ83). OpenResearchLeaves58CM is OpenResearchLeaves57 without
gonzalezRotgerThm512X6RCF and with the five CM-branch inputs. The bundles between it and the first weak (_r5) bundle
that carry the field are copied without it (`_cm`): OpenResearchLeaves56, 55, 54 (TailZ81-83) and the bost-gr9 copies
GR9.OpenResearchLeaves36EBCF, GR9.OpenResearchLeaves35EBCF (TailZ80); each conversion is a verbatim copy with the
field's line dropped; the last conversion is the weak-row conversion of CMFoldRebase/R5GR9*.lean with its input type
switched to the `_cm` bundle.
"""
import re, os, glob
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), '../../..'))
FIELD = 'gonzalezRotgerThm512X6RCF'


def read(p): return open(os.path.join(ROOT, p)).read().split('\n')


def block(lines, start_pat):
    i = [k for k, l in enumerate(lines) if re.match(start_pat, l)]
    assert len(i) == 1, (start_pat, len(i))
    a = i[0]; b = a + 1
    while b < len(lines) and (lines[b].startswith(' ') or lines[b].strip() == '' and b + 1 < len(lines) and lines[b + 1].startswith(' ')):
        b += 1
    return lines[a:b]


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


def header(blk, new):
    assert blk[0].rstrip().endswith(' where'), blk[0]
    return [new] + blk[1:]


z80 = read('ZInQKernel/OneProof/H/TailZ80.lean')
z81 = read('ZInQKernel/OneProof/H/TailZ81.lean')
z82 = read('ZInQKernel/OneProof/H/TailZ82.lean')
z83 = read('ZInQKernel/OneProof/H/TailZ83.lean')
r5txt = []
for p in sorted(glob.glob(os.path.join(ROOT, 'ZInQKernel/Contrib/OneProof/CMFoldRebase/R5GR9*.lean'))):
    r5txt += open(p).read().split('\n')

CM_FIELDS = [
    '  /-- cm-branch (GLUE, open): A8 at a CM fibre and the matrix units (diophantine_zq.tex L520-562, L581-586). -/',
    '  cmFibreSplit : CMBranch.CMFibreSplit',
    '  /-- cm-branch (leaf, printed form, pending review): Fowler, Math. Proc. Cambridge Philos. Soc. 180 (2026), Prop. 2.7 (L588-590). -/',
    '  fowlerProp27 : CMBranch.FowlerProp27',
    '  /-- cm-branch (leaf, ELLIOT-literature, pending review): the degree of a singular modulus, #Pic(R) <= [L:Q] (L586-587). -/',
    '  cmjDegree : CMBranch.CMjDegree',
    '  /-- cm-branch (leaf, ELLIOT-literature, pending review): CM elliptic curves have potentially good reduction (L596-597). -/',
    '  cmPotentialGood : CMBranch.CMPotentialGood',
    '  /-- cm-branch (leaf, consequence form, pending review): Barquero-Sanchez et al., Res. Number Theory 3 (2017), Eq. (6.2) (L600-605). -/',
    '  cmHeight62 : CMBranch.CMHeight62']

s58 = drop_field(block(z83, r'^structure OpenResearchLeaves57 '), FIELD)
s58 = ['/-- `OpenResearchLeaves57` without `gonzalezRotgerThm512X6RCF` (read by no theorem of the CM-branch route,',
       'cm-branch2 §3) and with the five CM-branch inputs (`CMBranch.CMInputs3`; cm-fold-rebase). -/',
       'structure OpenResearchLeaves58CM : Prop where'] + s58[1:] + CM_FIELDS
s56 = drop_field(block(z82, r'^structure OpenResearchLeaves56 '), FIELD)
s56 = ['/-- `OpenResearchLeaves56` without `gonzalezRotgerThm512X6RCF` (cm-fold-rebase). -/',
       'structure OpenResearchLeaves56_cm : Prop where'] + s56[1:]
s55 = drop_field(block(z81, r'^structure OpenResearchLeaves55 '), FIELD)
s55 = ['/-- `OpenResearchLeaves55` without `gonzalezRotgerThm512X6RCF` (cm-fold-rebase). -/',
       'structure OpenResearchLeaves55_cm : Prop where'] + s55[1:]
s54 = drop_field(block(z80, r'^structure OpenResearchLeaves54 '), FIELD)
s54 = ['/-- `OpenResearchLeaves54` without `gonzalezRotgerThm512X6RCF` (cm-fold-rebase). -/',
       'structure OpenResearchLeaves54_cm : Prop where'] + s54[1:]
c56 = header(drop_field(block(z83, r'^theorem openResearchLeaves56_of_OpenResearchLeaves57 '), FIELD),
             'theorem openResearchLeaves56_cm_of_58CM (n : OpenResearchLeaves58CM) : OpenResearchLeaves56_cm where')
c55 = header(drop_field(block(z82, r'^theorem openResearchLeaves55_of_OpenResearchLeaves56 '), FIELD),
             'theorem openResearchLeaves55_cm_of_56_cm (n : OpenResearchLeaves56_cm) : OpenResearchLeaves55_cm where')
c54 = header(drop_field(block(z81, r'^theorem openResearchLeaves54_of_OpenResearchLeaves55 '), FIELD),
             'theorem openResearchLeaves54_cm_of_55_cm (n : OpenResearchLeaves55_cm) : OpenResearchLeaves54_cm where')
# bost-gr9 copies (namespace HDec.HSyn.GR9)
s36 = drop_field(block(z80, r'^structure OpenResearchLeaves36EBCF '), 'gonzalezRotgerThm512X6')
s36 = ['/-- `GR9.OpenResearchLeaves36EBCF` without `gonzalezRotgerThm512X6` (cm-fold-rebase). -/',
       'structure OpenResearchLeaves36EBCF_cm : Prop where'] + s36[1:]
s35 = drop_field(block(z80, r'^structure OpenResearchLeaves35EBCF '), 'gonzalezRotgerThm512X6')
s35 = ['/-- `GR9.OpenResearchLeaves35EBCF` without `gonzalezRotgerThm512X6` (cm-fold-rebase). -/',
       'structure OpenResearchLeaves35EBCF_cm : Prop where'] + s35[1:]
c36 = header(drop_field(block(z80, r'^theorem openResearchLeaves36EBCF_of_OpenResearchLeaves53 '), 'gonzalezRotgerThm512X6'),
             'theorem openResearchLeaves36EBCF_cm_of_54_cm (n : _root_.HDec.HSyn.OpenResearchLeaves54_cm) (t : OpenTextbookLeaves18) : OpenResearchLeaves36EBCF_cm where')
c35 = header(drop_field(block(z80, r'^theorem openResearchLeaves35_of_OpenResearchLeaves36_eb_k954_cf '), 'gonzalezRotgerThm512X6'),
             'theorem openResearchLeaves35_cm_of_36_cm (n : OpenResearchLeaves36EBCF_cm) (t : OpenTextbookLeaves16) (l : OpenAddedLeaves26) : OpenResearchLeaves35EBCF_cm where')
c34 = block(r5txt, r'^theorem _root_\.HDec\.HSyn\.GR9\.openResearchLeaves34_of_OpenResearchLeaves35_eb_cf_r5 ')
c34 = header(c34, 'theorem openResearchLeaves34_r5_of_35_cm (n : OpenResearchLeaves35EBCF_cm) (t : OpenTextbookLeaves16) : _root_.HDec.HSyn.GR9.OpenResearchLeaves34EBCF_r5 where')

hdr = '''import ZInQKernel.Contrib.OneProof.CMFoldRebase.R5GR9
import ZInQKernel.Contrib.OneProof.CMBranch.CoxProof

/-! # cm-fold-rebase: the CM-branch fold's next generation on main's top (generated by `scratch/cm-fold-rebase/gen/gen_open77.py`)

`OpenResearchLeaves58CM` is main's `OpenResearchLeaves57` (TailZ83) without `gonzalezRotgerThm512X6RCF` (read by no theorem
of the CM-branch route, cm-branch2 §3) and with the five CM-branch inputs (`CMBranch.CMInputs3`: the GLUE `cmFibreSplit`
and the leaves `fowlerProp27`, `cmjDegree`, `cmPotentialGood`, `cmHeight62`). The bundles down to the first weak bundle
that carry the field are copied without it (`_cm`); each conversion is a verbatim copy with the field's line dropped, the
last one the weak-row conversion of `CMFoldRebase/R5GR9*.lean`. `sixContactMin_of_open77_cm` is the top theorem of the
fold: `ZInQ.SixContactMin` from the open statements alone, with `CoxProperLattice` proved
(`CMBranch.coxProperLattice_proof`; cox-lattice's `CMBranch.CoxLattice.coxProperLattice_proof` is an alternative). -/

set_option maxHeartbeats 1000000
set_option linter.style.longLine false

'''
body = ['namespace HDec', 'namespace HSyn', 'noncomputable section', '']
for blk in (s58, s56, s55, s54, c56, c55, c54):
    body += blk + ['']
body += ['end', 'end HSyn', 'end HDec', '', 'namespace HDec', 'namespace HSyn.GR9', 'noncomputable section', '']
for blk in (s36, s35, c36, c35, c34):
    body += blk + ['']
body += ['end', 'end HSyn.GR9', 'end HDec', '']
top = '''namespace HDec
namespace HSyn

/-- **G0 with only the open statements, the CM branch of the manuscript in place of NoCM** (cm-fold-rebase: cm-branch2's
fold on main's top `sixContactMin_of_open76`): `gonzalezRotgerThm512X6RCF` removed; `CMFibreSplit`, `FowlerProp27`,
`CMjDegree`, `CMPotentialGood`, `CMHeight62` added; `CoxProperLattice` proved. -/
theorem sixContactMin_of_open77_cm (r : OpenResearchLeaves58CM) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves27) :
    ZInQ.SixContactMin :=
  let t16 := openTextbookLeaves16_of_OpenTextbookLeaves17 (openTextbookLeaves17_of_OpenTextbookLeaves18 t)
  let l26 := openAddedLeaves26_of_OpenAddedLeaves27 l
  _root_.HDec.HSyn.GR9.sixContactMin_of_open48_eb_k954_cm2_r5
    (c := ⟨r.cmFibreSplit, r.fowlerProp27, r.cmjDegree, r.cmPotentialGood, r.cmHeight62,
      CMBranch.coxProperLattice_proof⟩)
    (_root_.HDec.HSyn.GR9.openResearchLeaves31_of_OpenResearchLeaves32_eb_cf_r5
      (_root_.HDec.HSyn.GR9.openResearchLeaves32_of_OpenResearchLeaves33_eb_cf_r5
        (_root_.HDec.HSyn.GR9.openResearchLeaves33_of_OpenResearchLeaves34_eb_cf_r5
          (GR9.openResearchLeaves34_r5_of_35_cm (GR9.openResearchLeaves35_cm_of_36_cm
            (GR9.openResearchLeaves36EBCF_cm_of_54_cm
              (openResearchLeaves54_cm_of_55_cm (openResearchLeaves55_cm_of_56_cm (openResearchLeaves56_cm_of_58CM r)))
              t) t16 l26) t16) t16))) t16 l26

end HSyn
end HDec

#print axioms HDec.HSyn.sixContactMin_of_open77_cm
'''
open(os.path.join(ROOT, 'ZInQKernel/Contrib/OneProof/CMFoldRebase/Open77.lean'), 'w').write(hdr + '\n'.join(body) + '\n' + top)
print('ok', len(body))
