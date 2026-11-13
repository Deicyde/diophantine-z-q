import ZInQKernel.Contrib.G9.LocalModel

/-!
# G9 without the weight clause: what R10's Lean form gives alone

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-derham, 2026-11-13).

`g9_partial`: from `G9Bridge.AbVarBaseChange` and R10 (`PkgI4.DeRhamComparison`) alone, i.e.
without `G9Bridge.R10Weights`, the data of `G9Glue` give: `r|G_{ℚ_ℓ}` is de Rham
(`LocalIsDeRham`), and over the same finite coefficient field its Hodge–Tate multiplicities at
`0` and at `−1` are `1`. What is missing for `HasHTWeightsAtSelf ℓ {0, −1}` is exactly the
vanishing of the multiplicities at the other weights (finding F1 of docs/research/g9-derham.md).
-/

namespace ZInQ.Contrib.G9

set_option linter.unusedSectionVars false

open PkgI4 G0Galois Module
open scoped TensorProduct

noncomputable section

section Mult

variable (p : ℕ) [Fact p.Prime] (F : Type*) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
  [IsGalois ℚ_[p] F] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]
  {E : IntermediateField ℚ_[p] (PadicAlgCl p)} [FiniteDimensional ℚ_[p] E]

/-- One Hodge–Tate multiplicity: `htMultOver ρ w = 2M ⇒ htMult ρE w = M`. -/
theorem core_htMult (ρ : Representation ℚ_[p] (Field.absoluteGaloisGroup F) V)
    (ρE : GQp p →* GL (Fin 2) E)
    (eE : E ⊗[ℚ_[p]] V ≃ₗ[E] (Fin 2 → E) × (Fin 2 → E))
    (he : ∀ σ x, eE ((ρ σ).baseChange E x) =
      ((matRep p ρE (gfToGqp p F σ)).prodMap (matRep p ρE (gfToGqp p F σ))) (eE x))
    (w : ℤ) (M : ℕ) (hM : htMultOver p ρ w = 2 * M) : htMult p ρE w = M := by
  have hd : 0 < finrank ℚ_[p] E := Module.finrank_pos
  have hf : 0 < finrank ℚ_[p] F := Module.finrank_pos
  obtain ⟨hc, hdvd⟩ := core_count p F (htAct p (-w)) (cpEmb p) (htAct_semi p (-w)) ρ ρE eE he
  rw [htMultOver, htSpaceOver_eq_DspRep] at hM
  rw [htMult, htSpace_eq_DspMat]
  obtain ⟨k, hk⟩ := hdvd
  rw [hk, Nat.mul_div_cancel_left _ hf] at hM
  rw [hk, hM] at hc
  have h1 : finrank ℚ_[p] F * (finrank ℚ_[p] E * (2 * M)) =
      finrank ℚ_[p] F * (2 * finrank ℚ_[p] (Dsp (htAct p (-w)) (matRep p ρE) Set.univ)) := by
    calc finrank ℚ_[p] F * (finrank ℚ_[p] E * (2 * M))
        = finrank ℚ_[p] E * (finrank ℚ_[p] F * (2 * M)) := by ring
      _ = _ := hc
      _ = _ := by ring
  have h2 := Nat.eq_of_mul_eq_mul_left hf h1
  have h3 : finrank ℚ_[p] (Dsp (htAct p (-w)) (matRep p ρE) Set.univ) =
      finrank ℚ_[p] E * M := by
    rw [mul_left_comm] at h2; omega
  rw [h3, Nat.mul_div_cancel_left _ hd]

end Mult

/-- **G9 from base change and R10 alone** (no weight clause): de Rham, and multiplicity `1` at
the weights `0` and `−1`. -/
theorem g9_partial (hBC : G9Bridge.AbVarBaseChange) (hR10 : PkgI4.DeRhamComparison)
    (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ))
    (hdim : A.dim = 2) (hint : Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e) :
    PkgI4.LocalIsDeRham ℓ 2 (r.restrictLocal ℓ) ∧
      ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ)) (_ : FiniteDimensional ℚ_[ℓ] E)
        (ρE : GQp ℓ →* GL (Fin 2) E),
        (∀ σ, Matrix.GeneralLinearGroup.map (algebraMap E (PadicAlgCl ℓ)) (ρE σ) =
          r.restrictLocal ℓ σ) ∧
        htMult ℓ ρE 0 = 1 ∧ htMult ℓ ρE (-1) = 1 := by
  obtain ⟨F, _, _, _, _, A', j, c, g, hdim', hc, hg⟩ :=
    localModel_of_abVarBaseChange hBC K A ℓ hdim
  obtain ⟨hdR, h0, h1⟩ := hR10 ℓ F A' 2 (by rw [hdim']; rfl)
  obtain ⟨ιB, hιB⟩ := fieldEmbBdR ℓ F
  let cb : PadicAlgCl ℓ ⊗[ℚ_[ℓ]] A'.V ℓ ≃ₗ[PadicAlgCl ℓ] PadicAlgCl ℓ ⊗[ℚ_[ℓ]] A.V ℓ :=
    LinearEquiv.baseChange ℚ_[ℓ] (PadicAlgCl ℓ) _ _ c
  let e' := (cb.trans e).trans (twistPair r g)
  have hcb : ∀ σ x, cb ((A'.galRep ℓ σ).baseChange (PadicAlgCl ℓ) x) =
      tate A ℓ (j σ) (cb x) := by
    intro σ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      change cb (a ⊗ₜ (A'.galRep ℓ σ v)) = (A.galRep ℓ (j σ)).baseChange (PadicAlgCl ℓ) (cb (a ⊗ₜ v))
      simp only [cb, LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul, hc]
    | add x x' hx hx' => rw [map_add, map_add, hx, hx', map_add, map_add]
  have he' : ∀ σ x, e' ((A'.galRep ℓ σ).baseChange (PadicAlgCl ℓ) x) =
      ((r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).mulVec (e' x).1,
        (r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)).mulVec
          (e' x).2) := by
    intro σ x
    have hR : (r.restrictLocal ℓ (gfToGqp ℓ F σ) : Matrix (Fin 2) (Fin 2) (PadicAlgCl ℓ)) =
        r.mat (decomp ℓ (gfToGqp ℓ F σ)) := rfl
    have hconj : r.mat g⁻¹ * r.mat (resQ K (j σ)) =
        r.mat (decomp ℓ (gfToGqp ℓ F σ)) * r.mat g⁻¹ := by
      rw [hg σ, galoisRep_mat_mul, galoisRep_mat_mul, ← mul_assoc, ← mul_assoc,
        galoisRep_mat_inv_mul, one_mul]
    simp only [e', LinearEquiv.trans_apply, hcb, twistPair_apply, hint _ (cb x), hR,
      Matrix.mulVec_mulVec, hconj]
  obtain ⟨E, hE, ρE, eE, hmap, he⟩ :=
    coef_descent ℓ F (A'.galRep ℓ) (r.restrictLocal ℓ) e' he'
  exact ⟨⟨E, hE, ρE, hmap, core_dR_F ℓ F ιB hιB (A'.galRep ℓ) ρE eE he hdR⟩,
    E, hE, ρE, hmap, core_htMult ℓ F (A'.galRep ℓ) ρE eE he 0 1 (by rw [h0]),
    core_htMult ℓ F (A'.galRep ℓ) ρE eE he (-1) 1 (by rw [h1])⟩

end

end ZInQ.Contrib.G9

#print axioms ZInQ.Contrib.G9.core_htMult
#print axioms ZInQ.Contrib.G9.g9_partial
