import ZInQKernel.Contrib.G9.I4Layer
import ZInQKernel.Contrib.OneProof.DeRhamHTMult.TateSen

/-! # The Tate–Sen bound for `(ℂ_p(i) ⊗_{ℚ_p} V)^{G_{ℚ_p}}`

For a finite-dimensional `ℚ_p`-vector space `V` with linear maps `r σ` (`σ ∈ G_{ℚ_p}`), the spaces
`H_i = {y ∈ ℂ_p ⊗ V | (χ(σ)^i σ ⊗ r σ) y = y}` are finite-dimensional and
`Σ_{i ∈ J} dim_{ℚ_p} H_i ≤ dim_{ℚ_p} V`, given Tate's two theorems over `ℚ_p`
(`hT`: `ℂ_p(i)^{G} = 0` for `i ≠ 0`; `hA`: `ℂ_p^{G} = ℚ_p`).
-/

set_option autoImplicit false

namespace DeRhamHTMult

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 Module
open scoped TensorProduct

noncomputable section

variable (p : ℕ) [Fact p.Prime]

theorem cycPow_zero' (σ : GQp p) : cycPow p σ 0 = 1 := by
  simp [cycPow]

theorem cycPow_add' (σ : GQp p) (a b : ℤ) :
    cycPow p σ (a + b) = cycPow p σ a * cycPow p σ b := by
  simp only [cycPow, zpow_add, Units.val_mul, PadicInt.coe_mul]

/-- `σ` on `ℂ_p`, `ℚ_p`-linearly. -/
def cpL (σ : GQp p) : ℂ_[p] →ₗ[ℚ_[p]] ℂ_[p] where
  toFun := cpAct p σ
  map_add' := map_add _
  map_smul' c x := by
    rw [RingHom.id_apply, Algebra.smul_def, map_mul, cpAct_algebraMap, ← Algebra.smul_def]

variable {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [FiniteDimensional ℚ_[p] V]
  (r : GQp p → V →ₗ[ℚ_[p]] V)

/-- `σ ⊗ r σ` on `ℂ_p ⊗ V`, additively. -/
def sAct (σ : GQp p) : ℂ_[p] ⊗[ℚ_[p]] V →+ ℂ_[p] ⊗[ℚ_[p]] V :=
  (TensorProduct.map (cpL p σ) (r σ)).toAddMonoidHom

theorem sAct_smul (σ : GQp p) (c : ℂ_[p]) (y : ℂ_[p] ⊗[ℚ_[p]] V) :
    sAct p r σ (c • y) = cpAct p σ c • sAct p r σ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [TensorProduct.smul_tmul']
    change (cpAct p σ (c • a)) ⊗ₜ[ℚ_[p]] (r σ v) =
      cpAct p σ c • ((cpAct p σ a) ⊗ₜ[ℚ_[p]] (r σ v))
    rw [smul_eq_mul, map_mul, TensorProduct.smul_tmul', smul_eq_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

variable (H : ℤ → Submodule ℚ_[p] (ℂ_[p] ⊗[ℚ_[p]] V))

/-- **The Tate–Sen bound** for the twisted invariants of `ℂ_p ⊗ V`. -/
theorem sum_finrank_twisted_le
    (hT : ∀ i : ℤ, i ≠ 0 → ∀ x : ℂ_[p], (∀ σ, cycPow p σ i • cpAct p σ x = x) → x = 0)
    (hA : ∀ x : ℂ_[p], (∀ σ, cpAct p σ x = x) → ∃ a : ℚ_[p], x = algebraMap ℚ_[p] ℂ_[p] a)
    (hH : ∀ i, ∀ y ∈ H i, ∀ σ, cycPow p σ i • TensorProduct.map (cpL p σ) (r σ) y = y)
    (J : Finset ℤ) : ∑ i ∈ J, finrank ℚ_[p] (H i) ≤ finrank ℚ_[p] V := by
  have h := sum_finrank_le (L := ℂ_[p]) (fun σ => cpAct p σ) (sAct p r)
    (fun i σ => cycPow p σ i) H (sAct_smul p r) (cycPow_zero' p)
    (fun a b σ => cycPow_add' p σ a b) hT hA hH J
  rwa [Module.finrank_baseChange] at h

theorem finiteDimensional_twisted_cp
    (hT : ∀ i : ℤ, i ≠ 0 → ∀ x : ℂ_[p], (∀ σ, cycPow p σ i • cpAct p σ x = x) → x = 0)
    (hA : ∀ x : ℂ_[p], (∀ σ, cpAct p σ x = x) → ∃ a : ℚ_[p], x = algebraMap ℚ_[p] ℂ_[p] a)
    (hH : ∀ i, ∀ y ∈ H i, ∀ σ, cycPow p σ i • TensorProduct.map (cpL p σ) (r σ) y = y)
    (i : ℤ) : FiniteDimensional ℚ_[p] (H i) :=
  finiteDimensional_twisted (L := ℂ_[p]) (fun σ => cpAct p σ) (sAct p r)
    (fun i σ => cycPow p σ i) H (sAct_smul p r) (cycPow_zero' p)
    (fun a b σ => cycPow_add' p σ a b) hT hA hH i

end

end DeRhamHTMult
