import ZInQKernel.Contrib.R10.Amend
import ZInQKernel.Contrib.G9.LocalModel

/-!
# G9 from the amended R10 (and base change of abelian varieties)

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task r10-amend, 2026-11-13).

g9-derham proved `g9Glue_of_abVarBaseChange : AbVarBaseChange → R10Weights → G9Glue`
(`ZInQKernel/Contrib/G9/LocalModel.lean`). With the amended leaf `DeRhamComparisonHT`
(`Amend.lean`), whose weight clause is `R10Weights`, this gives

* `g9Glue_of_HT : AbVarBaseChange → DeRhamComparisonHT → G9Glue`;
* `G9GlueHT`: g0-mod-galois's `G9Glue` with its R10 hypothesis replaced by the amended leaf and
  the unused T23 hypothesis dropped; `g9GlueHT_of_abVarBaseChange : AbVarBaseChange → G9GlueHT`.
  The proof is g9-derham's `g9Glue_of_fieldEmb` (`Reduction.lean`) with the old R10 and
  `R10Weights` both read off the amended leaf. `G9GlueHT` implies `G9GlueHT'`, the same statement
  with T23 kept, which is `G9Glue` with R10 replaced by its amendment.
-/

namespace ZInQ.Contrib.R10

set_option linter.unusedSectionVars false

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.G9.G0Galois Module
open scoped TensorProduct

noncomputable section

/-- **G9 with the amended R10** (g0-mod-galois's `G9Glue`, R10 replaced by `DeRhamComparisonHT`,
T23 dropped since the proof does not use it). -/
def G9GlueHT : Prop :=
  DeRhamComparisonHT →
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)),
    A.dim = 2 → Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e → G9Out r

/-- `G9Glue` verbatim, with `PkgI4.DeRhamComparison` replaced by `DeRhamComparisonHT`. -/
def G9GlueHT' : Prop :=
  DeRhamComparisonHT → (∀ (p : ℕ) [Fact p.Prime], PkgI4.T23_FontaineClosure p) →
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (r : GaloisRep ℓ 2)
    (e : Vb A ℓ ≃ₗ[PadicAlgCl ℓ] (Fin 2 → PadicAlgCl ℓ) × (Fin 2 → PadicAlgCl ℓ)),
    A.dim = 2 → Intertwines (tate A ℓ) (fun σ => r.mat (resQ K σ)) e → G9Out r

theorem g9GlueHT'_of_g9GlueHT (h : G9GlueHT) : G9GlueHT' :=
  fun hR _ => h hR

/-- `G9Glue` from base change and the amended R10. -/
theorem g9Glue_of_HT (hBC : G9Bridge.AbVarBaseChange) (hR : DeRhamComparisonHT) : G9Glue :=
  g9Glue_of_abVarBaseChange hBC (r10Weights_of_HT hR)

/-- **G9 with the amended R10, from base change of abelian varieties.** g9-derham's proof of
`g9Glue_of_fieldEmb`, with `LocalModel` from `AbVarBaseChange`, `F' ⊆ B_dR` from `fieldEmbBdR`,
and both the old R10 and `R10Weights` from `DeRhamComparisonHT`. -/
theorem g9GlueHT_of_abVarBaseChange (hBC : G9Bridge.AbVarBaseChange) : G9GlueHT := by
  intro hRHT K _ _ A ℓ _ r e hdim hint
  have hLM := localModel_of_abVarBaseChange hBC
  have hR10 := deRhamComparison_of_HT hRHT
  have hW := r10Weights_of_HT hRHT
  obtain ⟨F, _, _, _, _, A', j, c, g, hdim', hc, hg⟩ := hLM K A ℓ hdim
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
  have hw : ∀ w : ℤ, w ≠ 0 → w ≠ -1 → htMultOver ℓ (A'.galRep ℓ) w = 0 :=
    fun w hw0 hw1 => hW ℓ F A' w hw0 hw1
  exact ⟨⟨E, hE, ρE, hmap, core_dR_F ℓ F ιB hιB (A'.galRep ℓ) ρE eE he hdR⟩,
    ⟨E, hE, ρE, hmap, core_ht ℓ F (A'.galRep ℓ) ρE eE he h0 h1 hw⟩⟩

end

end ZInQ.Contrib.R10

#print axioms ZInQ.Contrib.R10.g9GlueHT'_of_g9GlueHT
#print axioms ZInQ.Contrib.R10.g9Glue_of_HT
#print axioms ZInQ.Contrib.R10.g9GlueHT_of_abVarBaseChange
