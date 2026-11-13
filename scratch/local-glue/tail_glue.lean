
/-! ## §9 (local-glue). The tail of `ModularConstituent` with the local glue on `A/K` (proved) -/

namespace G0ModNewform

open PkgI4 (Qbar GQ LiesOver IsArithFrob CF coeff IsNewform IsNormalizedEigenform GaloisRep
  GaloisChar)
open PkgI3 PkgI3.AbVar LeafModCurves C9Rhof
open CategoryTheory AlgebraicGeometry

/-- **G13-G16 with G15 fed by G7's data and the local glue as Props on `A/K` (GLUE, proved).**
As local-data's `modularConstituent_tail_L`, with `G8LocalPack` replaced by `G7LocalPackK`
(`g8LocalPack_of_K`). -/
theorem modularConstituent_tail_K (lv : NewformLeaves) (hJac : JacobianExists ℚ)
    (hX : X1ModelExists)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧
      G7LocalPackK 5 D.r5 (fun p => p ≠ 5) ∧ G7LocalPackK 3 D.r3 (fun p => p = 5) ∧
      G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5 ∧
      G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) := by
  obtain ⟨D, h12, hc, h5, h3, h11a, h11b⟩ := h
  exact modularConstituent_tail_L lv hJac hX hSw hL8 hAd A u
    ⟨D, h12, hc, g8LocalPack_of_K h5, g8LocalPack_of_K h3, h11a, h11b⟩

/-- **G13-G16 with the local glue in leaf-and-bridge form (GLUE, proved).** As
`modularConstituent_tail_K`, with `G7LocalPackR` and the leaves R6, I2-Tors (`g7LocalPackK_of_R`). -/
theorem modularConstituent_tail_R (lv : NewformLeaves) (hJac : JacobianExists ℚ)
    (hX : X1ModelExists)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧
      G7LocalPackR 5 D.r5 (fun p => p ≠ 5) ∧ G7LocalPackR 3 D.r3 (fun p => p = 5) ∧
      G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5 ∧
      G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) := by
  obtain ⟨D, h12, hc, h5, h3, h11a, h11b⟩ := h
  exact modularConstituent_tail_K lv hJac hX hSw hL8 hAd A u
    ⟨D, h12, hc, g7LocalPackK_of_R hR6 hTors (fun _ h => h) h5,
      g7LocalPackK_of_R hR6 hTors (fun p h => by rw [h]; norm_num) h3, h11a, h11b⟩

/-- **G13-G16 with the local glue as the glue Props of §7d (GLUE, proved).** As
`modularConstituent_tail_K`, with `G7LocalPackD` (`KerWild`, `DescentPts` at `p ≤ 5`, `BetaTwist2`
at `p = 2`) and the leaves R6, I2-Tors (`g8LocalPack_of_D`). -/
theorem modularConstituent_tail_D (lv : NewformLeaves) (hJac : JacobianExists ℚ)
    (hX : X1ModelExists)
    (hSw : ∀ (p : ℕ) [Fact p.Prime], LadicCond.SwanIndependent (p := p))
    (hL8 : LadicCond.SwanIntegral) (hAd : ∀ (p : ℕ) [Fact p.Prime], LadicCond.AdaptedExists (p := p))
    (hR6 : ObjBridge.RaynaudCriterion) (hTors : ObjBridge.TorsionStructure)
    {L : Type} [Field L] [NumberField L] (A : AbVar L) (u : ℚ)
    (h : ∃ D : ModData L A, G12Spec D ∧ G14TraceCompat D ∧
      G7LocalPackD 5 D.r5 (fun p => p ≠ 5) ∧ G7LocalPackD 3 D.r3 (fun p => p = 5) ∧
      G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r5 ∧
      G0Galois.G11Out (GlueDescent.ramSet ZInQ.Mult.S_mul u) D.r3) :
    ∃ (N : ℕ) (J : AbVar ℚ), 0 < N ∧ IsJ1 N J ∧
      (N : ℝ) ≤ ZInQ.heightQ ZInQ.heightD * (ZInQ.contactSupport ZInQ.Mult.S_mul u : ℝ) ^ 2 ∧
      CommonConstituent A (J.baseChange L) := by
  obtain ⟨D, h12, hc, h5, h3, h11a, h11b⟩ := h
  exact modularConstituent_tail_L lv hJac hX hSw hL8 hAd A u
    ⟨D, h12, hc, g8LocalPack_of_D hR6 hTors (fun _ h => h) h5,
      g8LocalPack_of_D hR6 hTors (fun p h => by rw [h]; norm_num) h3, h11a, h11b⟩

end G0ModNewform

#print axioms G0ModNewform.modularConstituent_tail_K
#print axioms G0ModNewform.modularConstituent_tail_R
#print axioms G0ModNewform.modularConstituent_tail_D
