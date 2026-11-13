
/-! ## §4. The tail of `ModularConstituent` with `G15RamG` replaced by its pieces (proved) -/

namespace G0ModNewform

open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep
  GaloisChar)
open PkgI3 PkgI3.AbVar LeafModCurves C9Rhof
open CategoryTheory AlgebraicGeometry

/-- **G13-G16 with G15's open Prop reduced (GLUE, proved).** As `modularConstituent_tail_G`, with
`G15RamG D u` replaced by g15-ram's pieces on `D` (`G15Ram.LocalData`, G11's output); all the
local-field glue is proved (`G15Ram.g15RamG_of_localData`). -/
theorem modularConstituent_tail_R (lv : NewformLeaves) (hJac : JacobianExists ℚ)
    (hX : X1ModelExists)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧
      (∀ (p : ℕ) (hp : p.Prime), p ≠ 5 → @G15Ram.LocalData p ⟨hp⟩ 5 _ D.r5) ∧
      G15Ram.LocalData 5 D.r3 ∧
      G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5 ∧
      G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) := by
  obtain ⟨D, h12, hc, h5, h3, h11a, h11b⟩ := h
  exact modularConstituent_tail_G lv hJac hX hSw hL8 hAd A u
    ⟨D, h12, hc, G15Ram.g15RamG_of_localData D u h5 h3 h11a h11b⟩

end G0ModNewform

#print axioms G0ModNewform.modularConstituent_tail_G
#print axioms G0ModNewform.modularConstituent_tail_R
