import ZInQKernel.Contrib.OneProof.DeRhamRange
import ZInQKernel.OneProof.H.TailT

/-! # Fontaine's de Rham closure on the actual B_dR model

The fixed-field theorem already proved for finite local fields supplies its
`ℚ_p` instance, so the established Tannakian closure needs no literature
input here. This is genuine de Rham closure, not Hodge–Tate closure.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

open _root_.ZInQ.Contrib.G9 _root_.ZInQ.Contrib.G9.PkgI4
open _root_.ZInQ.Contrib.HodgeSplit

set_option maxHeartbeats 1200000 in
/-- The original Galois action on the actual `B_dR` has fixed field `ℚ_p`. -/
theorem bdrInvariantsQp_proof (p : ℕ) [Fact p.Prime] : BdRInvariants p := by
  intro x hx
  have hfix : x ∈ DeRhamPrint.bdrFix p ℚ_[p] := fun σ => hx (gfToGqp p ℚ_[p] σ)
  obtain ⟨y, hy⟩ := (DeRhamPrint.Range.mem_bdrFix_iff p ℚ_[p] x).mp hfix
  obtain ⟨c, rfl⟩ := (equivFieldF p ℚ_[p]).surjective y
  refine ⟨c, ?_⟩
  rw [← hy, show equivFieldF p ℚ_[p] c = algebraMap ℚ_[p] (fieldF p ℚ_[p]) c from
    (equivFieldF p ℚ_[p]).commutes c, AlgHom.commutes]
  rfl

/-- Full Fontaine closure for `ℚ_p`-linear matrix representations, from the
proved fixed-field theorem. No separate `T23` hypothesis remains here. -/
theorem fontaineClosureQp_proof (p : ℕ) [Fact p.Prime] :
    _root_.ZInQ.Contrib.G9.PkgI4.T23_FontaineClosure p :=
  t23_of_fontaine p (fontaineDRTannakian_of_bdrInvariants p (bdrInvariantsQp_proof p))

end HDec.G0Galois.C8Conrad.Manuscript
