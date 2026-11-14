"""Generate ZInQKernel/OneProof/H/TailZ5.lean and TailZ6.lean. TailZ5: leaf-fold9's lemmas (scratch/leaf-fold9/Lemmas.lean.part, compiled
first as scratch/leaf-fold9/test/R1recT.lean) and the bundles OpenResearchLeaves9, OpenTextbookLeaves9 with the
maps to leaf-fold8's bundles. Field blocks are copied from TailZ4.lean, so every kept field keeps its text."""
import re
src = open('ZInQKernel/OneProof/H/TailZ4.lean').read()

def fields(name):
    i = src.index('structure ' + name)
    j = src.index('\n\n', i)
    out, cur = [], []
    for line in src[i:j].split('\n')[1:]:
        cur.append(line)
        m = re.match(r'^  ([A-Za-z0-9_]+) : ', line)
        if m:
            out.append((m.group(1), '\n'.join(cur))); cur = []
    return out

DROP_R = {'r1rec': 'r1rec_of_rep r.r1r2', 'r5': 'r5fp_of_rep r.r1r2',
          'r15': '_root_.ModularSplit.deligneSerreConseq_of_ds r.dsThm966',
          'r7b': '_root_.ReductSplit.serreTatePotentialGood_final r.serreTateThm2 t.mumfordTorsionAlgClosed',
          'r8': "_root_.ReductSplit.grothendieckMonodromy_final' r.semistableReductionDVR r.semistableUnipotent\n    r.neronSchemeModelExistsDVR t.mumfordTorsionAlgClosed",
          'r5count': '_root_.ShimuraSplit.r5fpCount_of_points r.gonzalezRotgerCountX6'}
NEW_R = '''  /-- reduct-split, r7b: Serre–Tate 1968 Thm 2 as printed (potential good reduction iff the image of inertia on
  `T_ℓ A` is finite; RISK: if printed for complete `K`, a consequence). -/
  serreTateThm2 : _root_.ReductSplit.SerreTateThm2
  /-- reduct-split, r8: SGA 7 IX Thm 3.6 over a DVR (semistable reduction after a finite extension, at every place
  above `O`). -/
  semistableReductionDVR : _root_.ReductSplit.SemistableReductionDVR
  /-- reduct-split, r8: SGA 7 IX Prop. 3.5, "semistable ⇒ `(σ - 1)² = 0` on `T_ℓ`" (weakest reading). -/
  semistableUnipotent : _root_.ReductSplit.SemistableUnipotent
  /-- reduct-split, r8: BLR §1.4 Thm 3 over a DVR (scheme form). -/
  neronSchemeModelExistsDVR : _root_.ReductSplit.NeronSchemeModelExistsDVR
  /-- shimura-split, r5count: González–Rotger 2006 Prop. 5.6 at `(D, N) = (6, 1)` on the points of one canonical
  coarse witness `X₆` (`#CM(R) = 2^{b(k)} h(R)`; the audit read Prop. 5.6). -/
  gonzalezRotgerCountX6 : _root_.ShimuraSplit.GonzalezRotgerCountX6'''
NEW_R_NAMES = ['serreTateThm2', 'semistableReductionDVR', 'semistableUnipotent', 'neronSchemeModelExistsDVR',
               'gonzalezRotgerCountX6']
DROP_T = {'t33': '_root_.ZInQ.Contrib.CloudW07JacobiansCurves.JacobianExists_proof',
          'normalModelOfFunctionFieldQ': '_root_.ZInQ.Contrib.CloudW07JacobiansCurves.NormalModelOfFunctionFieldQ_proof'}
rf, tf = fields('OpenResearchLeaves8'), fields('OpenTextbookLeaves8')
assert len(rf) == 31 and len(tf) == 20
assert all(k in dict(rf) for k in DROP_R) and all(k in dict(tf) for k in DROP_T)
lemmas = open('scratch/leaf-fold9/Lemmas.lean.part').read()

out = []
out.append('''import ZInQKernel.OneProof.H.TailZ4
import ZInQKernel.Contrib.FrobChain.Rigidity
import ZInQKernel.Contrib.CloudW07JacobiansCurves.JacobianExists
import ZInQKernel.Contrib.CloudW07JacobiansCurves.NormalModel
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-! # OneProof H, leaf-fold9: the next bundle generation

`HDec.HSyn.sixContactMin_of_open9 (r : OpenResearchLeaves9) (t : OpenTextbookLeaves9) (l : OpenAddedLeaves8)
(g : OpenGlue7)` proves `ZInQ.SixContactMin` by filling leaf-fold8's bundles (`sixContactMin_of_open8`, `TailZ4`)
from the new ones; the bundles and that theorem are in `TailZ6`, this module has the proofs. Folded (docs/research/leaf-fold9.md lists every field):

* the research fields `r1rec` (R1(d), `LeafQM.AV.R1rec`) and `r5` (R5, `LeafQM.AV.R5fp`) are **proved from the
  research field `r1r2`** (`LeafAdopt.R1R2fpRep`), whose witness carries the same statements on residue fields of
  points (`R1recProps`, `R5ptProps`). The bridge is proved here (`ZInQ.LeafFold9`): on the fine witness the field of
  moduli of an object lies in the residue field of its point (`fieldOfModuli3_le`), and on the coarse witness the
  residue field of a point is the field of moduli of its pair (`residueImage_eq_fieldOfModuliPair`; uniqueness of
  base change by the kernel's rigidity `G0FibreSimple.rigidityHom`), with infinite Galois theory for `ℚ̄/ℚ` and
  `NumberField.discr_dvd_discr` for subfields;
* modular-split (`TailZ6`): the research field `r15` from the field `dsThm966`;
* cloud PR #11 (`ZInQKernel/Contrib/CloudW07JacobiansCurves/`): the textbook fields `t33`
  (`JacobianExists_proof`) and `normalModelOfFunctionFieldQ` (`NormalModelOfFunctionFieldQ_proof`).

No existing module is edited; every field that is not folded keeps leaf-fold8's type. -/
''')
out.append(lemmas.rstrip() + '\n')
out.append('''
namespace HDec

namespace HSyn

open CategoryTheory AlgebraicGeometry Limits

/-! ## R1(d) and R5 from the witness of `r1r2` -/

/-- **`R1rec` from `R1R2fpRep`**: the object `P` is the object at a point `y` of the fine witness (`Φ` is a
bijection), the witness's reciprocity clause makes `ℚ(y)` unramified above 5, and `fieldOfModuli3 P ⊆ ℚ(y)`. -/
theorem r1rec_of_rep (h : LeafAdopt.R1R2fpRep) : LeafQM.AV.R1rec := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, -, -, -, hrec, -, -, -⟩ := h
  intro P hcm
  have hy : Φ _ ((Φ _).symm (LeafQM.AV.M3.mk P)) = LeafQM.AV.M3.mk P := Equiv.apply_symm_apply _ _
  exact _root_.ZInQ.LeafFold9.unramifiedAbove5_mono (_root_.ZInQ.LeafFold9.fieldOfModuli3_le h1 _ P hy)
    (hrec _ P hy hcm)

/-- **`R5fp` from `R1R2fpRep`**: the pair `P` is the pair at a point `x` of the coarse witness (`Ψ` is a
bijection), the witness's González–Rotger clause is about `ℚ(x)`, and `ℚ(x)` is the field of moduli of `P`. -/
theorem r5fp_of_rep (h : LeafAdopt.R1R2fpRep) : LeafQM.AV.R5fp := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, -, -, h6, -, -, -, h5, -⟩ := h
  intro k _ _ _ hk R hR hc P hP
  have hx : Ψ (Ψ.symm (Quotient.mk _ P)) = Quotient.mk _ P := Equiv.apply_symm_apply _ _
  obtain ⟨h5a, h5b⟩ := h5 k hk R hR hc _ P hx hP
  have e := _root_.ZInQ.LeafFold9.residueImage_eq_fieldOfModuliPair h6 _ P hx
  refine ⟨?_, fun hne => (h5b hne).map fun φ => (IntermediateField.equivOfEq e).toAlgHom.comp φ⟩
  rw [← h5a]
  exact (IntermediateField.equivOfEq e).toLinearEquiv.finrank_eq.symm

end HSyn

end HDec
''')
z5 = ''.join(out)
r15 = open('scratch/modular-split/R15.lean').read().split('\n')
assert r15[0] == 'import ZInQKernel.OneProof.H.TailT' and r15[1] == 'import ZInQKernel.OneProof.H.LPrefix'
r15body = '\n'.join(l for l in r15[2:] if not l.startswith('#print')).strip('\n')
z6 = '''import ZInQKernel.OneProof.H.TailZ5

/-! # OneProof H, leaf-fold9: modular-split's row r15

modular-split's `scratch/modular-split/R15.lean` verbatim after its two import lines (`TailT`, `LPrefix`, both below
this module; `#print` dropped): `ModularSplit.deligneSerreConseq_of_ds : DSThm966 → HDec.HSyn.DeligneSerreConseq`
(row r15 from Deligne–Serre's printed theorem, already the field `dsThm966`). -/

''' + r15body + '\n'
red = open('scratch/reduct-split/Reduction.lean').read().split('\n')
nimp = 0
while red[nimp].startswith('import'):
    nimp += 1
redimports = '\n'.join(red[:nimp])
redbody = '\n'.join(l for l in red[nimp:] if not l.startswith('#print')).strip('\n')
z7 = redimports + '''

/-! # OneProof H, leaf-fold9: reduct-split's `Reduction.lean`

reduct-split's `scratch/reduct-split/Reduction.lean` verbatim (its imports kept; `#print` dropped). It proves the
rows r7b (`serreTatePotentialGood_final`) and r8 (`grothendieckMonodromy_final'`) from published-form leaves; the
rest of the file (r6, SS1-SS3, faltingsLemma5BC with their glue) is not used by the bundles. -/

''' + redbody + '\n'
cnt = open('scratch/shimura-split/Count.lean').read().split('\n')
assert cnt[0] == 'import ZInQKernel.HDecomp.QM.Leaves'
cntbody = '\n'.join(l for l in cnt[1:] if not l.startswith('#print')).strip('\n')
z8 = '''import ZInQKernel.HDecomp.QM.Leaves

/-! # OneProof H, leaf-fold9: shimura-split's `Count.lean`

shimura-split's `scratch/shimura-split/Count.lean` verbatim (its one import kept; `#print` dropped; kernel imports
only): `ShimuraSplit.r5fpCount_of_points : GonzalezRotgerCountX6 → LeafQM.AV.R5fpCount` (row r5count from
González–Rotger Prop. 5.6 on the points of the canonical `X₆`). -/

''' + cntbody + '\n'
out = ['''import ZInQKernel.OneProof.H.TailZ6
import ZInQKernel.OneProof.H.TailZ7
import ZInQKernel.OneProof.H.TailZ8

/-! # OneProof H, leaf-fold9: the bundles and `sixContactMin_of_open9`

The bundles `OpenResearchLeaves9`, `OpenTextbookLeaves9`, the maps to leaf-fold8's bundles and
`sixContactMin_of_open9`. The proofs used are in `TailZ5` (this task: `r1rec`, `r5` from `r1r2`), `TailZ6`
(modular-split: `r15`), `TailZ7` (reduct-split: `r7b`, `r8`), `TailZ8` (shimura-split: `r5count`) and the CloudW07 modules (`t33`,
`normalModelOfFunctionFieldQ`). docs/research/leaf-fold9.md lists every field. -/

namespace HDec

namespace HSyn

open CategoryTheory AlgebraicGeometry Limits

/-! ## The bundles -/

''']
out.append('/-- **The research leaves still open** (leaf-fold9): leaf-fold8\'s `OpenResearchLeaves8` without `r1rec`, `r5`\n(proved from `r1r2`, `r1rec_of_rep`, `r5fp_of_rep`) and `r15` (proved from `dsThm966`, modular-split\'s\n`deligneSerreConseq_of_ds`), and `r7b`, `r8` replaced by reduct-split\'s four published-form leaves\n(`ReductSplit.serreTatePotentialGood_final`, `grothendieckMonodromy_final\'`). %d fields. -/\nstructure OpenResearchLeaves9 : Prop where\n' % (len(rf) - len(DROP_R) + len(NEW_R_NAMES)))
out.append('\n'.join(b for k, b in rf if k not in DROP_R) + '\n' + NEW_R + '\n\n')
out.append('/-- **The textbook leaves still open** (leaf-fold9): leaf-fold8\'s `OpenTextbookLeaves8` without `t33` and\n`normalModelOfFunctionFieldQ` (proved by cloud PR #11, `ZInQKernel/Contrib/CloudW07JacobiansCurves/`). %d fields. -/\nstructure OpenTextbookLeaves9 : Prop where\n' % (len(tf) - len(DROP_T)))
out.append('\n'.join(b for k, b in tf if k not in DROP_T) + '\n\n')
out.append('/-! ## From the new bundles to leaf-fold8\'s -/\n\n')
out.append('/-- leaf-fold8\'s research bundle from leaf-fold9\'s. -/\ntheorem researchLeaves8_of_open9 (r : OpenResearchLeaves9) (t : OpenTextbookLeaves9) : OpenResearchLeaves8 where\n')
out.append('\n'.join('  %s := %s' % (k, DROP_R.get(k, 'r.' + k)) for k, _ in rf) + '\n\n')
out.append('/-- leaf-fold8\'s textbook bundle from leaf-fold9\'s. -/\ntheorem textbookLeaves8_of_open9 (t : OpenTextbookLeaves9) : OpenTextbookLeaves8 where\n')
out.append('\n'.join('  %s := %s' % (k, DROP_T.get(k, 't.' + k)) for k, _ in tf) + '\n\n')
out.append('''/-- **G0 with only the open leaves and the open glue** (leaf-fold9; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from `OpenResearchLeaves9` (%d), `OpenTextbookLeaves9` (%d), leaf-fold8's
`OpenAddedLeaves8` (14) and leaf-fold7's `OpenGlue7` (1, `QuotientP1Coordinate`). The table of every field is
`docs/research/leaf-fold9.md` §2. -/
theorem sixContactMin_of_open9 (r : OpenResearchLeaves9) (t : OpenTextbookLeaves9) (l : OpenAddedLeaves8)
    (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open8 (researchLeaves8_of_open9 r t) (textbookLeaves8_of_open9 t) l g

end HSyn

end HDec
''' % (len(rf) - len(DROP_R) + len(NEW_R_NAMES), len(tf) - len(DROP_T)))
open('ZInQKernel/OneProof/H/TailZ5.lean', 'w').write(z5)
open('ZInQKernel/OneProof/H/TailZ6.lean', 'w').write(z6)
open('ZInQKernel/OneProof/H/TailZ7.lean', 'w').write(z7)
open('ZInQKernel/OneProof/H/TailZ8.lean', 'w').write(z8)
open('ZInQKernel/OneProof/H/TailZ9.lean', 'w').write(''.join(out).replace("`grothendieckMonodromy_final'`). 30 fields.", "`grothendieckMonodromy_final'`), and `r5count` replaced by shimura-split's\n`GonzalezRotgerCountX6` (`ShimuraSplit.r5fpCount_of_points`). 30 fields.").replace("`TailZ8` (shimura-split: `r5count`) and the CloudW07 modules (`t33`,\n`normalModelOfFunctionFieldQ`)", "`TailZ8` (shimura-split: `r5count`)\nand the CloudW07 modules (`t33`, `normalModelOfFunctionFieldQ`)"))
print('written', len(z5), len(z6), len(z7), len(z8), sum(len(x) for x in out), 'bytes')
