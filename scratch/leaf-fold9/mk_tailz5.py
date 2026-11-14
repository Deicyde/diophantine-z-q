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
          'r15': '_root_.ModularSplit.deligneSerreConseq_of_ds r.dsThm966'}
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
out = ['''import ZInQKernel.OneProof.H.TailZ5

/-! # OneProof H, leaf-fold9 (bundles): `sixContactMin_of_open9`

First, modular-split's `scratch/modular-split/R15.lean` verbatim after its two import lines (`#print` dropped):
`ModularSplit.deligneSerreConseq_of_ds : DSThm966 → HDec.HSyn.DeligneSerreConseq` (row r15 from Deligne–Serre's
printed theorem, already the field `dsThm966`). Then the bundles `OpenResearchLeaves9`, `OpenTextbookLeaves9`, the
maps to leaf-fold8's bundles and `sixContactMin_of_open9`. -/

''' + r15body + '''

namespace HDec

namespace HSyn

open CategoryTheory AlgebraicGeometry Limits

/-! ## The bundles -/

''']
out.append('/-- **The research leaves still open** (leaf-fold9): leaf-fold8\'s `OpenResearchLeaves8` without `r1rec`, `r5`\n(proved from `r1r2`, `r1rec_of_rep`, `r5fp_of_rep`) and `r15` (proved from `dsThm966`, modular-split\'s\n`deligneSerreConseq_of_ds`). %d fields. -/\nstructure OpenResearchLeaves9 : Prop where\n' % (len(rf) - len(DROP_R)))
out.append('\n'.join(b for k, b in rf if k not in DROP_R) + '\n\n')
out.append('/-- **The textbook leaves still open** (leaf-fold9): leaf-fold8\'s `OpenTextbookLeaves8` without `t33` and\n`normalModelOfFunctionFieldQ` (proved by cloud PR #11, `ZInQKernel/Contrib/CloudW07JacobiansCurves/`). %d fields. -/\nstructure OpenTextbookLeaves9 : Prop where\n' % (len(tf) - len(DROP_T)))
out.append('\n'.join(b for k, b in tf if k not in DROP_T) + '\n\n')
out.append('/-! ## From the new bundles to leaf-fold8\'s -/\n\n')
out.append('/-- leaf-fold8\'s research bundle from leaf-fold9\'s. -/\ntheorem researchLeaves8_of_open9 (r : OpenResearchLeaves9) : OpenResearchLeaves8 where\n')
out.append('\n'.join('  %s := %s' % (k, DROP_R.get(k, 'r.' + k)) for k, _ in rf) + '\n\n')
out.append('/-- leaf-fold8\'s textbook bundle from leaf-fold9\'s. -/\ntheorem textbookLeaves8_of_open9 (t : OpenTextbookLeaves9) : OpenTextbookLeaves8 where\n')
out.append('\n'.join('  %s := %s' % (k, DROP_T.get(k, 't.' + k)) for k, _ in tf) + '\n\n')
out.append('''/-- **G0 with only the open leaves and the open glue** (leaf-fold9; no `sorry`, standard axioms).
`ZInQ.SixContactMin` follows from `OpenResearchLeaves9` (%d), `OpenTextbookLeaves9` (%d), leaf-fold8's
`OpenAddedLeaves8` (14) and leaf-fold7's `OpenGlue7` (1, `QuotientP1Coordinate`). The table of every field is
`docs/research/leaf-fold9.md` §2. -/
theorem sixContactMin_of_open9 (r : OpenResearchLeaves9) (t : OpenTextbookLeaves9) (l : OpenAddedLeaves8)
    (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open8 (researchLeaves8_of_open9 r) (textbookLeaves8_of_open9 t) l g

end HSyn

end HDec
''' % (len(rf) - len(DROP_R), len(tf) - len(DROP_T)))
open('ZInQKernel/OneProof/H/TailZ5.lean', 'w').write(z5)
open('ZInQKernel/OneProof/H/TailZ6.lean', 'w').write(''.join(out))
print('written', len(z5), sum(len(x) for x in out), 'bytes')
