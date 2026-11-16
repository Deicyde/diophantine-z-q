exec(open('/home/jackmccarthy/dzq-wt/pi0-prune/scratch/pi0-prune/tools/common.py').read())
OUT = '/home/jackmccarthy/dzq-wt/pi0-prune/ZInQKernel/Contrib/OneProof/Pi0Prune/Base.lean'
HEADER = r'''import ZInQKernel.OneProof.H.TailZ35

/-!
# pi0-prune (1/3): the row `R1R2fpRepW` (`R1R2fpRep` without `R1pi0Props`), its destructurers and producers

`HDec.LeafAdopt.R1R2fpRep` (LPrefix) ends with the clause `R1pi0Props X` (`X₆` geometrically connected). On the
single proof that clause is produced from the two fields `deligneComponentsX6PrintedAb` and `geomConnOfAlgClosure`
and read by nobody (triage2, probe `scratch/triage2/Pi0Use.lean`). This file defines

* `LeafAdopt.R1R2fpRepW`: `R1R2fpRep` without its last conjunct, with `R1R2fpRepW_of_rep : R1R2fpRep → R1R2fpRepW`;
* the destructurers (`R1R2fp_of_repW`, `r1rec_of_repW`, `r5fp_of_repW`, `pairsLift_of_repW`, ...) and the consumers
  of the row that are not bundle maps, copied verbatim from the chain with `R1R2fpRep` replaced by `R1R2fpRepW`
  (each copy names its source file and lines at base 43513d87);
* the producers: `r1r2fpRep_of_printedW`, which takes the base witness from González–Rotger's leaf
  (`GonzalezRotgerX6`) instead of Deligne's `π₀` with `GeomConnOfAlgClosure`.

No `sorry`; standard axioms only.
-/

set_option linter.all false
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace HDec.LeafAdopt

open CategoryTheory AlgebraicGeometry Limits
open LeafQM LeafQM.AV

/-- **`R1R2fpRep` without its last conjunct `R1pi0Props X`** (pi0-prune). The clause `R1pi0Props X` (`X₆`
geometrically connected) is never read on the single proof (triage2, `scratch/triage2/Pi0Use.lean`). -/
def R1R2fpRepW : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6PropsIff X Ψ π₆ ∧
      R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ

/-- The row `R1R2fpRep` implies its weak form. -/
theorem R1R2fpRepW_of_rep (h : R1R2fpRep) : R1R2fpRepW := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5, -⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5⟩

/-- `R1R2fp_of_rep` (LPrefix 5228-5231) with the weak row; the proof is unchanged. -/
theorem R1R2fp_of_repW (h : R1R2fpRepW) : R1R2fp := by
  obtain ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, h2, hr, hs, h5⟩ := h
  exact ⟨Y, Φ, X, Ψ, fY, π₆, h1, hh, h6, r2X6Props_of_iff h2, cmExists_of_iff h2 hs.1, hr, hs, h5⟩

end HDec.LeafAdopt
'''
SEGMENTS = [
  ('TailC.lean', [('fibreQMPeriod_main_rep', {})]),
  ('TailI.lean', [('propTSAll_of_pieces3', {})]),
  ('TailK.lean', [('periodMapGlue_of_leaves4', {})]),
  ('TailN.lean', [('heckeVertWitness_of_leaves5', {})]),
  ('TailO.lean', [('descend_main', {}), ('cmDescends_of', {})]),
  ('TailU.lean', [('r1b_of', {}), ('x6ConicModel_of', {}), ("r1b_of'", {})]),
  ('TailZ5.lean', [('r1rec_of_rep', {'subs': [('hrec, -, -, -⟩', 'hrec, -, -⟩')], 'note': 'pattern: one conjunct fewer'}), ('r5fp_of_rep', {'subs': [('h5, -⟩ := h', 'h5⟩ := h')], 'note': 'pattern: one conjunct fewer'})]),
  ('TailZ20.lean', [('pairsLift_of_rep', {'subs': [('hs, -, -⟩', 'hs, -⟩')], 'note': 'pattern: one conjunct fewer'}), ('coarseFactor_of_rep', {}), ("coarseFactor_of_rep'", {}), ('x6ConicModel_of_elkies', {}), ('x6ConicModel_of_elkies_t5', {})]),
]

FOOTER = open('/home/jackmccarthy/dzq-wt/pi0-prune/scratch/pi0-prune/tools/base_producers.lean').read()
