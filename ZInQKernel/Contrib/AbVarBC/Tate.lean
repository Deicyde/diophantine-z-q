import ZInQKernel.Contrib.AbVarBC.Dim
import ZInQKernel.Contrib.AbVarBC.Points
import ZInQKernel.HDecomp.I3Linalg.TateBC

/-!
# Base change of abelian varieties, III: Tate modules

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

For `A : PkgI3.AbVar K` (the kernel's abelian varieties, `ZInQKernel/HDecomp/Objects.lean`), a
field extension `L/K` and a `K`-embedding `κ : K̄ → L̄`:
* `ptBC A κ : A(K̄) →* A_L(L̄)` is injective (`ptBC_injective`) and Galois-natural
  (`ptBC_galAct`: if `κ ∘ τ = σ ∘ κ` for `τ ∈ G_K`, `σ ∈ G_L`);
* `tateBC A ℓ κ : T_ℓ(A) →ₗ[ℤ_ℓ] T_ℓ(A_L)` is injective and Galois-natural (`tateBC_galT`);
* it is bijective as soon as the `ℓ`-power torsion of `A_L(L̄)` comes from `A(K̄)`
  (`tateBC_bijective_of_torsionDescends`), or under leaf T26 `PkgI3.TateModuleFree`
  (`tateBC_bijective_of_tateModuleFree`, through the kernel glue `PkgI3.Tate.map_bijective` and
  `dim A_L = dim A`);
* `vBC A ℓ κ hb : V_ℓ(A_L) ≃ₗ[ℚ_ℓ] V_ℓ(A)` with `vBC_galRep`: it intertwines `ρ_{A_L}(σ)` with
  `ρ_A(τ)`.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace ZInQ.Contrib.AbVarBC

/-! ## §1. Tate modules along an injective map whose `ℓ`-power torsion is in the image -/

section TateGen

variable {ℓ : ℕ} [Fact ℓ.Prime] {M N : Type*} [AddCommGroup M] [AddCommGroup N]

/-- If `φ : M → N` is injective and every `ℓ`-power torsion element of `N` is in its image,
`T_ℓ(φ)` is bijective. -/
theorem tate_map_bijective_of_torsion (φ : M →+ N) (hφ : Function.Injective φ)
    (htors : ∀ (n : ℕ) (q : N), (ℓ ^ n) • q = 0 → ∃ p, φ p = q) :
    Function.Bijective (PkgI3.Tate.map (ℓ := ℓ) φ) := by
  refine ⟨PkgI3.Tate.map_injective φ hφ, fun x => ?_⟩
  have hx : ∀ n, ∃ p, φ p = x.1 n := fun n =>
    htors n (x.1 n) (PkgI3.Tate.pow_smul_eq_zero x.2 n)
  choose y hy using hx
  refine ⟨⟨y, ?_, fun n => ?_⟩, ?_⟩
  · apply hφ
    rw [hy, x.2.1, map_zero]
  · apply hφ
    rw [map_nsmul, hy, hy, x.2.2 n]
  · apply Subtype.ext
    funext n
    exact hy n

end TateGen

/-! ## §2. Points and Tate modules of a base change -/

/-- An element of `G_K` as an automorphism of `K̄`. -/
abbrev galK {K : Type*} [Field K] (σ : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ

section BC

variable {K L : Type} [Field K] [Field L] [Algebra K L] (A : PkgI3.AbVar K)
  (κ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)

/-- `A(K̄) → A(L̄) ≅ A_L(L̄)`. -/
noncomputable def ptBC : A.Pt (AlgebraicClosure K) →* (A.baseChange L).Pt (AlgebraicClosure L) :=
  (bcPt A (AlgebraicClosure L)).symm.toMonoidHom.comp (extPt A κ)

theorem ptBC_injective : Function.Injective (ptBC A κ) :=
  (bcPt A (AlgebraicClosure L)).symm.injective.comp (extPt_injective A κ)

/-- Galois-naturality of `ptBC`. -/
theorem ptBC_galAct (τ : Field.absoluteGaloisGroup K) (σ : Field.absoluteGaloisGroup L)
    (h : ∀ x, κ (galK τ x) = galK σ (κ x)) (p : A.Pt (AlgebraicClosure K)) :
    ptBC A κ (A.galAct τ p) = (A.baseChange L).galAct σ (ptBC A κ p) := by
  have h1 := extPt_galAct A κ τ ((σ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L).restrictScalars K)
    h p
  have h2 := bcPt_galAct A (AlgebraicClosure L) σ
    ((bcPt A (AlgebraicClosure L)).symm (extPt A κ p))
  rw [MulEquiv.apply_symm_apply] at h2
  change (bcPt A (AlgebraicClosure L)).symm (extPt A κ (A.galAct τ p)) =
    (A.baseChange L).galAct σ ((bcPt A (AlgebraicClosure L)).symm (extPt A κ p))
  rw [h1, ← h2, MulEquiv.symm_apply_apply]

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- `T_ℓ(A) → T_ℓ(A_L)`. -/
noncomputable def tateBC : A.T ℓ →ₗ[ℤ_[ℓ]] (A.baseChange L).T ℓ :=
  PkgI3.Tate.map (MonoidHom.toAdditive (ptBC A κ))

theorem tateBC_injective : Function.Injective (tateBC A κ ℓ) :=
  PkgI3.Tate.map_injective _ (ptBC_injective A κ)

/-- Galois-naturality of `tateBC`. -/
theorem tateBC_galT (τ : Field.absoluteGaloisGroup K) (σ : Field.absoluteGaloisGroup L)
    (h : ∀ x, κ (galK τ x) = galK σ (κ x)) (x : A.T ℓ) :
    tateBC A κ ℓ (A.galT τ x) = (A.baseChange L).galT σ (tateBC A κ ℓ x) := by
  apply Subtype.ext
  funext n
  exact congrArg Additive.ofMul (ptBC_galAct A κ τ σ h (Additive.toMul (x.1 n)))

/-- **Descent of `ℓ`-power torsion** (the content of "`A[ℓⁿ]` is finite étale"): every
`ℓ`-power torsion point of `A_L(L̄)` comes from `A(K̄)`. -/
def TorsionDescends : Prop :=
  ∀ (n : ℕ) (q : (A.baseChange L).Pt (AlgebraicClosure L)), q ^ (ℓ ^ n) = 1 →
    ∃ p, ptBC A κ p = q

theorem tateBC_bijective_of_torsionDescends (h : TorsionDescends A κ ℓ) :
    Function.Bijective (tateBC A κ ℓ) :=
  tate_map_bijective_of_torsion _ (ptBC_injective A κ) fun n q hq => h n (Additive.toMul q) hq

/-- **Under leaf T26 (`TateModuleFree`), `T_ℓ(A) → T_ℓ(A_L)` is bijective** (`ℓ ≠ char K`). -/
theorem tateBC_bijective_of_tateModuleFree (hT : PkgI3.TateModuleFree) (hℓ : (ℓ : K) ≠ 0) :
    Function.Bijective (tateBC A κ ℓ) := by
  have hℓL : (ℓ : L) ≠ 0 := by
    rw [← map_natCast (algebraMap K L)]
    exact (map_ne_zero_iff _ (algebraMap K L).injective).mpr hℓ
  obtain ⟨hfree, hfin, hrk⟩ := hT K A ℓ hℓ
  obtain ⟨-, hfinL, hrkL⟩ := hT L (A.baseChange L) ℓ hℓL
  rw [PkgI3.AbVar.dim_baseChange] at hrkL
  have hr : Module.finrank ℤ_[ℓ] (A.T ℓ) = Module.finrank ℤ_[ℓ] ((A.baseChange L).T ℓ) := by
    have := hrk.trans hrkL.symm
    exact_mod_cast this
  exact PkgI3.Tate.map_bijective _ (ptBC_injective A κ) hr

/-- **`V_ℓ(A_L) ≅ V_ℓ(A)`**, from a bijective `tateBC`. -/
noncomputable def vBC (hb : Function.Bijective (tateBC A κ ℓ)) :
    (A.baseChange L).V ℓ ≃ₗ[ℚ_[ℓ]] A.V ℓ :=
  ((LinearEquiv.ofBijective (tateBC A κ ℓ) hb).baseChange ℤ_[ℓ] ℚ_[ℓ] _ _).symm

/-- `vBC` intertwines `ρ_{A_L}(σ)` with `ρ_A(τ)` when `κ ∘ τ = σ ∘ κ`. -/
theorem vBC_galRep (hb : Function.Bijective (tateBC A κ ℓ)) (τ : Field.absoluteGaloisGroup K)
    (σ : Field.absoluteGaloisGroup L) (h : ∀ x, κ (galK τ x) = galK σ (κ x)) (v : (A.baseChange L).V ℓ) :
    vBC A κ ℓ hb ((A.baseChange L).galRep ℓ σ v) = A.galRep ℓ τ (vBC A κ ℓ hb v) := by
  set e := (LinearEquiv.ofBijective (tateBC A κ ℓ) hb).baseChange ℤ_[ℓ] ℚ_[ℓ] _ _ with he
  have key : ∀ w : A.V ℓ, e (A.galRep ℓ τ w) = (A.baseChange L).galRep ℓ σ (e w) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul a t =>
      change e ((A.galT τ).baseChange ℚ_[ℓ] (a ⊗ₜ t)) =
        ((A.baseChange L).galT σ).baseChange ℚ_[ℓ] (e (a ⊗ₜ t))
      rw [LinearMap.baseChange_tmul, he, LinearEquiv.baseChange_tmul, LinearEquiv.baseChange_tmul,
        LinearMap.baseChange_tmul, LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply,
        tateBC_galT A κ ℓ τ σ h]
    | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂, map_add, map_add]
  show e.symm ((A.baseChange L).galRep ℓ σ v) = A.galRep ℓ τ (e.symm v)
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, key, LinearEquiv.apply_symm_apply]

end BC

end ZInQ.Contrib.AbVarBC
