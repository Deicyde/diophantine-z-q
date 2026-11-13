import ZInQKernel.Contrib.GZTheta.Split
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.BadPrime.Vanishing

/-!
# gz-theta: `η(4τ)²η(8τ)²` is new at level 32

The associated newform `g` of `f₁ = η(4τ)²η(8τ)²` (Tau Ceti, Diamond–Shurman 5.8.4) has level
`M ∣ 32`. If `M = 32` then `f₁ = g` (Diamond–Shurman 5.8.2) is new. Otherwise:
* `M = 1` is impossible (`S₂(SL₂(ℤ)) = 0`, Mathlib);
* for `M ∈ {2, 4, 8, 16}`, `f₁(τ) = g(τ) − a₂(g) g(2τ)` (the coefficients agree at odd `n`, and
  `a_{2n}(g) = a₂(g) a_n(g)`); applying the Fricke involution `τ ↦ −1/(32τ)`, under which
  `f₁(−1/(32τ)) = −32 τ² f₁(τ)` while `g(−1/(Mτ)) = c τ² g(τ)`, gives
  `−32 f₁(τ) = c (32/M)² g((32/M)τ) − a₂ c (16/M)² g((16/M)τ)`; dividing by `q` and letting
  `Im τ → ∞`, the left side tends to `−32` and the right side to `0` (for `M = 16`, `a₂(g) = 0`
  because `4 ∣ 16`: Tau Ceti, Miyake 4.6.17).
-/

open Complex Filter ModularForm UpperHalfPlane CongruenceSubgroup HeckeRing.GL2
  Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped Real Topology MatrixGroups

noncomputable section

namespace ZInQ.GZTheta

open ZInQ.Contrib.HeckeFE

/-! ### The Fricke involution on `f₁` -/

/-- `f₁(z) = η(4z)² η(8z)²` on `ℂ`. -/
def F₁ (z : ℂ) : ℂ := η (4 * z) ^ 2 * η (8 * z) ^ 2

theorem F₁_fricke {z : ℂ} (hz : 0 < z.im) : F₁ (-1 / (32 * z)) = -32 * z ^ 2 * F₁ z := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have h8 : 0 < (8 * z).im := by simp; exact hz
  have h4 : 0 < (4 * z).im := by simp; exact hz
  unfold F₁
  rw [show 4 * (-1 / (32 * z)) = -1 / (8 * z) by field_simp; ring,
    show 8 * (-1 / (32 * z)) = -1 / (4 * z) by field_simp; ring,
    eta_sq_neg_inv h8, eta_sq_neg_inv h4]
  ring_nf
  rw [I_sq]
  ring

/-! ### The Fricke involution on a newform -/

theorem newform_fricke {M : ℕ} [NeZero M] (g : Newform M 2) (hχ : g.χ = 1) :
    ∃ c : ℂ, ∀ (z : ℂ) (hz : 0 < z.im) (hz' : 0 < (-1 / ((M : ℂ) * z)).im),
      g.toCuspForm ⟨-1 / ((M : ℂ) * z), hz'⟩ = c * z ^ 2 * g.toCuspForm ⟨z, hz⟩ := by
  have hfr := g.normalizedFrickeOperatorCusp_eq_frickeSign_smul hχ
  set ε := g.frickeSign hχ
  have hnorm : TauCeti.atkinLehnerNormalizer M 2 = 1 := by
    simp [TauCeti.atkinLehnerNormalizer]
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  refine ⟨ε * M, fun z hz hz' => ?_⟩
  have h := congrArg (fun F : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2 => (⇑F) ⟨z, hz⟩) hfr
  simp only [TauCeti.coe_normalizedFrickeOperatorCusp, hnorm, one_smul] at h
  rw [ModularForm.slash_apply] at h
  have hdet : (0 : ℝ) < ((TauCeti.frickeGL ℝ M).det : ℝ) := TauCeti.val_det_frickeGL_pos
  have hσ : ∀ w : ℂ, σ (TauCeti.frickeGL ℝ M) w = w := fun w => by
    simp only [σ, if_pos hdet]; rfl
  have hpt : (TauCeti.frickeGL ℝ M • (⟨z, hz⟩ : ℍ)) = ⟨-1 / ((M : ℂ) * z), hz'⟩ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hdet, UpperHalfPlane.num, UpperHalfPlane.denom,
      TauCeti.coe_frickeGL]
    simp
  have hden : denom (TauCeti.frickeGL ℝ M) (⟨z, hz⟩ : ℍ) = (M : ℂ) * z := by
    rw [UpperHalfPlane.denom, TauCeti.coe_frickeGL]
    simp
  have hdetv : |((TauCeti.frickeGL ℝ M).det : ℝ)| = M := by
    rw [TauCeti.val_det_frickeGL, abs_of_nonneg (Nat.cast_nonneg _)]
  rw [hσ, hpt, hden, hdetv, CuspForm.smul_apply, smul_eq_mul] at h
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  generalize g.toCuspForm ⟨-1 / ((M : ℂ) * z), hz'⟩ = A at h ⊢
  generalize g.toCuspForm ⟨z, hz⟩ = B at h ⊢
  push_cast at h
  have hne : ((M : ℂ) * z) ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero hM0 hz0)
  simp only [zpow_one, zpow_neg, zpow_two] at h
  field_simp at h
  linear_combination h

end ZInQ.GZTheta
