import ZInQKernel.Contrib.G9.G9

/-!
# G9 with the full weight multiset `{0, −1}`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

R10's Lean form (`PkgI4.DeRhamComparison`) fixes the Hodge–Tate multiplicities of `V_p(A)` at
the weights `0` and `−1` only. N5's conclusion "the Hodge–Tate weights of `r` are `0, −1`", in
pkg-I4's form `HasHTWeights p r {0, −1}` (every multiplicity), also needs the vanishing of the
other multiplicities of `V_p(A)`. That vanishing is part of the published theorem (the Hodge–Tate
decomposition `ℂ_p ⊗ V_p(A) ≅ ℂ_p^g ⊕ ℂ_p(1)^g`, Faltings 1988 / Fontaine 1982 / Tate 1967,
together with Tate's `ℂ_p(i)^{G_F} = 0` for `i ≠ 0`; numbers UNVERIFIED), but not of R10's Lean
form. It is stated here as the separate Prop `DeRhamComparisonWeights` (a candidate strengthening
of R10's Lean form), and `g9_hasHTWeights` takes it as an extra hypothesis.
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open PkgI4 Module
open scoped TensorProduct

noncomputable section

/-- **R10, weight clause** (not in R10's Lean form; part of the published statement): `V_p(A)`
has no Hodge–Tate weight other than `0` and `−1`. -/
def DeRhamComparisonWeights : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : PkgI4.I3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ w : ℤ, w ≠ 0 → w ≠ -1 → htMultOver p (A.galRep p) w = 0

section Weights

variable (p : ℕ) [Fact p.Prime]

theorem htMult_eq_zero_of_R10w (hR10w : DeRhamComparisonWeights) (F : Type) [Field F]
    [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F] (A : PkgI4.I3.AbVar F)
    (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (C : Type*) [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    (r : GQp p →* GL (Fin 2) C)
    (e : C ⊗[ℚ_[p]] A.V p ≃ₗ[C] (Fin 2 → C) × (Fin 2 → C))
    (he : ∀ σ v, e (GlueI3.repBaseChange C (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).2))
    (w : ℤ) (hw0 : w ≠ 0) (hw1 : w ≠ -1) : htMult p r w = 0 := by
  have hz := hR10w p F A 2 hA w hw0 hw1
  have hF : 0 < finrank ℚ_[p] F := Module.finrank_pos
  set i := -w
  set act := cpActHom p i
  set nV := finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F)) (A.galRep p) Set.univ)
  have hnV : finrank ℚ_[p] (htSpaceOver p (A.galRep p) i) = nV := by
    rw [htSpaceOver_eq_DspAct]
  have hdvd : finrank ℚ_[p] F ∣ nV := by
    have := finrank_dvd_Dsp_of_emb (act.comp (gfToGqp p F)) (fun σ => A.galRep p σ) Set.univ
      (iotaCp p F) (fun σ _ x b => by
        have hk : gfToGqp p F σ ∈ (gammaF p F).ker := by
          rw [← range_gfToGqp]; exact ⟨σ, rfl⟩
        rw [MonoidHom.mem_ker] at hk
        change act (gfToGqp p F σ) _ = _
        rw [cpActHom_semi, hk]
        rfl)
    rwa [finrank_fieldF] at this
  obtain ⟨k, hk⟩ := hdvd
  have hnV0 : nV = 0 := by
    have : htMultOver p (A.galRep p) w = k := by
      rw [htMultOver, hnV, hk, Nat.mul_div_cancel_left _ hF]
    rw [hz] at this
    rw [hk, ← this, mul_zero]
  by_contra hne
  have hG : 0 < finrank ℚ_[p] (Dsp act (rRep p r) Set.univ) := by
    rw [htMult, htSpace_eq_DspAct] at hne
    exact Nat.pos_of_ne_zero fun h0 => hne (by rw [h0, Nat.zero_div])
  have hdes := descent_finrank act (rRep p r) (iotaCp p F) (gammaF p F) (gammaF_surjective p F)
    (cpActHom_semi p F i)
  rw [Dsp_ker_gammaF, finrank_fieldF] at hdes
  have hU : 0 < finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F))
      (fun σ => rRep p r (gfToGqp p F σ)) Set.univ) := by
    change 0 < finrank ℚ_[p] (Dsp (act.comp (gfToGqp p F))
      ((rRep p r).comp (gfToGqp p F)) Set.univ)
    rw [hdes]
    positivity
  have := overF_pos_rev (act.comp (gfToGqp p F)) (C := C) (fun σ => A.galRep p σ)
    (fun σ => rRep p r (gfToGqp p F σ)) Set.univ e (fun σ x => he σ x) hU
  change 0 < nV at this
  omega

/-- **G9 with the full weight multiset.** From R10, its weight clause
`DeRhamComparisonWeights`, and G8's local output: `r` is de Rham with Hodge–Tate weights exactly
`{0, −1}` (pkg-I4's `HasHTWeights`). -/
theorem g9_hasHTWeights (hR10 : DeRhamComparison) (hR10w : DeRhamComparisonWeights)
    (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]
    (A : PkgI4.I3.AbVar F) (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (C : Type*) [Field C] [Algebra ℚ_[p] C] [FiniteDimensional ℚ_[p] C]
    (r : GQp p →* GL (Fin 2) C)
    (e : C ⊗[ℚ_[p]] A.V p ≃ₗ[C] (Fin 2 → C) × (Fin 2 → C))
    (he : ∀ σ v, e (GlueI3.repBaseChange C (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) C).mulVec (e v).2)) :
    IsDeRham p r ∧ HasHTWeights p r {0, -1} := by
  obtain ⟨hdr, h0, h1⟩ := g9_deRham p hR10 F A hA C r e he
  refine ⟨hdr, fun w => ?_⟩
  by_cases hw0 : w = 0
  · subst hw0; rw [h0]; decide
  by_cases hw1 : w = -1
  · subst hw1; rw [h1]; decide
  rw [htMult_eq_zero_of_R10w p hR10w F A hA C r e he w hw0 hw1]
  simp [hw0, hw1]

/-- The `ℚ̄_p`-valued form (`LocalIsDeRham`, `LocalHasHTWeights`) for a coefficient field
`E ⊆ ℚ̄_p`. -/
theorem g9_local (hR10 : DeRhamComparison) (hR10w : DeRhamComparisonWeights)
    (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] [IsGalois ℚ_[p] F]
    (A : PkgI4.I3.AbVar F) (hA : A.dim = ((2 : ℕ) : WithBot ℕ∞))
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] E]
    (r : GQp p →* GL (Fin 2) E) (ρ : GQp p →* GL (Fin 2) (PadicAlgCl p))
    (hρ : ∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl p)) (r σ) = ρ σ)
    (e : E ⊗[ℚ_[p]] A.V p ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ v, e (GlueI3.repBaseChange E (A.galRep p) σ v) =
      ((r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) E).mulVec (e v).1,
        (r (gfToGqp p F σ) : Matrix (Fin 2) (Fin 2) E).mulVec (e v).2)) :
    LocalIsDeRham p 2 ρ ∧ LocalHasHTWeights p ρ {0, -1} := by
  obtain ⟨hdr, hht⟩ := g9_hasHTWeights p hR10 hR10w F A hA E r e he
  exact ⟨⟨E, inferInstance, r, hρ, hdr⟩, ⟨E, inferInstance, r, hρ, hht⟩⟩

end Weights

end

end ZInQ.Contrib.G9
