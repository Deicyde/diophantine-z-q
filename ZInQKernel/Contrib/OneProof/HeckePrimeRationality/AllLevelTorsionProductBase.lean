import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelPrincipalForms

/-!
# Homogeneous products of torsion forms on `Γ(N)`

For a positive level `N`, a length `k` and admissible pairs `v₀, …, v_{k-1}` (each not divisible
by `N` in both coordinates), the pointwise product `∏ᵢ F_{vᵢ}` of the torsion functions
`F_v = Torsion.torsionLogDerivative N v.1 v.2` is a modular form of weight `k` on `Γ(N)`
(`productForm`), built from the weight-one forms `principalForm` by the multiplication of modular
forms. The empty product is the constant form `1` of weight `0`.

Under `SL(2, ℤ)` the product transforms by the row action on every label:
`(∏ᵢ F_{vᵢ}) ∣[k] γ = ∏ᵢ F_{vᵢ γ}` (`prodFun_slash`, `productForm_slash`).

No statement about nonvanishing, spanning or rationality is made.
-/

noncomputable section

open ModularGroup
open scoped Real UpperHalfPlane MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.AllLevelProducts

open CongruenceSubgroup Matrix.SpecialLinearGroup
open Torsion AllLevelForms AllLevelPrincipal
open ThetaFiveTorsion (act)

set_option quotPrecheck false in
local notation "ΓP" N => (Gamma N).map (mapGL ℝ)

variable {N : ℕ}

/-- The product function `τ ↦ ∏ᵢ F_{vᵢ}(τ)`. -/
def prodFun (N : ℕ) {k : ℕ} (v : Fin k → ℤ × ℤ) : ℍ → ℂ := fun τ => ∏ i, F N (v i) τ

theorem prodFun_apply {k : ℕ} (v : Fin k → ℤ × ℤ) (τ : ℍ) :
    prodFun N v τ = ∏ i, torsionLogDerivative N (v i).1 (v i).2 τ := rfl

theorem prodFun_zero (v : Fin 0 → ℤ × ℤ) : prodFun N v = 1 := by
  funext τ; simp [prodFun]

theorem prodFun_succ {k : ℕ} (v : Fin (k + 1) → ℤ × ℤ) :
    prodFun N v = F N (v 0) * prodFun N (Fin.tail v) := by
  funext τ
  simp only [prodFun, Pi.mul_apply, Fin.prod_univ_succ, Fin.tail]

/-- **The product form** `∏ᵢ F_{vᵢ}` of weight `k` on `Γ(N)`. -/
def productForm (N : ℕ) (hN : 0 < N) :
    (k : ℕ) → (v : Fin k → ℤ × ℤ) → (∀ i, Good N (v i)) → ModularForm (ΓP N) (k : ℤ)
  | 0, _, _ => ModularForm.mcast (by simp) (1 : ModularForm (ΓP N) 0)
  | k + 1, v, hv =>
    ModularForm.mcast (by push_cast; ring)
      ((principalForm N hN (v 0).1 (v 0).2 (hv 0)).mul
        (productForm N hN k (Fin.tail v) (fun i => hv i.succ)))

theorem coe_productForm (hN : 0 < N) :
    ∀ (k : ℕ) (v : Fin k → ℤ × ℤ) (hv : ∀ i, Good N (v i)),
      ⇑(productForm N hN k v hv) = prodFun N v
  | 0, v, hv => by
    rw [prodFun_zero]
    funext τ
    rfl
  | k + 1, v, hv => by
    rw [prodFun_succ, ← coe_productForm hN k (Fin.tail v) (fun i => hv i.succ)]
    rfl

/-- Evaluation: the product form is the pointwise product of the torsion functions. -/
theorem productForm_apply (hN : 0 < N) (k : ℕ) (v : Fin k → ℤ × ℤ) (hv : ∀ i, Good N (v i))
    (τ : ℍ) :
    productForm N hN k v hv τ = ∏ i, torsionLogDerivative N (v i).1 (v i).2 τ := by
  rw [coe_productForm]; rfl

/-- Admissibility is preserved by the row action on every label. -/
theorem good_act_tuple {k : ℕ} {v : Fin k → ℤ × ℤ} (hv : ∀ i, Good N (v i)) (γ : SL(2, ℤ)) :
    ∀ i, Good N (act (v i) γ) := fun i => good_act (hv i) γ

/-- **Covariance of the product function**: `(∏ᵢ F_{vᵢ}) ∣[k] γ = ∏ᵢ F_{vᵢ γ}`. -/
theorem prodFun_slash (hN : 0 < N) (γ : SL(2, ℤ)) :
    ∀ (k : ℕ) (v : Fin k → ℤ × ℤ), (∀ i, Good N (v i)) →
      prodFun N v ∣[(k : ℤ)] γ = prodFun N (fun i => act (v i) γ)
  | 0, v, _ => by
    rw [prodFun_zero, prodFun_zero]
    exact ModularForm.is_invariant_one γ
  | k + 1, v, hv => by
    rw [prodFun_succ, prodFun_succ, show ((k + 1 : ℕ) : ℤ) = 1 + (k : ℤ) by push_cast; ring,
      ModularForm.mul_slash_SL2, F_slash hN γ (v 0) (hv 0),
      prodFun_slash hN γ k (Fin.tail v) (fun i => hv i.succ)]
    rfl

/-- **Covariance of the product form** under `SL(2, ℤ)`. -/
theorem productForm_slash (hN : 0 < N) (k : ℕ) (v : Fin k → ℤ × ℤ) (hv : ∀ i, Good N (v i))
    (γ : SL(2, ℤ)) :
    ⇑(productForm N hN k v hv) ∣[(k : ℤ)] γ =
      ⇑(productForm N hN k (fun i => act (v i) γ) (good_act_tuple hv γ)) := by
  rw [coe_productForm, coe_productForm]
  exact prodFun_slash hN γ k v hv

/-- The empty product is the constant `1`. -/
theorem productForm_zero (hN : 0 < N) (v : Fin 0 → ℤ × ℤ) (hv : ∀ i, Good N (v i)) (τ : ℍ) :
    productForm N hN 0 v hv τ = 1 := by
  rw [productForm_apply]; simp

end ZInQ.Contrib.HeckePrimeRationality.AllLevelProducts
