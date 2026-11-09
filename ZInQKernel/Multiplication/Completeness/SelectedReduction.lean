import ZInQKernel.Multiplication.Completeness.TestsLocal
import ZInQKernel.Model.Descent.Reduction
import ZInQKernel.Model.Descent.PointCounts

/-!
# Formal multiples at a selected prime

Let `p` be an odd prime, `r² = 2` in `𝔽_p` with `75 - 53 r ≠ 0`, and `π` a prime of `ℤ[s]` with
`(π) = ker(a + b s ↦ a + b r)`. Reduction modulo `π` is a homomorphism `E(K₀) → Ẽ_r(𝔽_p)` onto a
group of order `d = pointCount p (-(75 - 53 r)²)`, so `d ∣ h` forces `[h]P₀` into the kernel of
reduction, that is into the formal neighbourhood `W₁` at `π`.
-/

namespace ZInQ.Mult

open WeierstrassCurve WeierstrassCurve.Affine

variable {p : ℕ} [Fact p.Prime]

/-- The residue of `A = -d²` at the prime `(p, s - r)` is `-(75 - 53 r)²`. -/
theorem res_neg_genD_sq {r : ZMod p} (hr : r ^ 2 = 2) {π : Zs} (hπ : Prime π)
    (hπr : ∀ a, residueAt r hr a = 0 ↔ π ∣ a) :
    res π (residueAt r hr) (-genD ^ 2) = -(75 - 53 * r) ^ 2 := by
  rw [neg_genD_sq_eq_toK0, res_toK0 hπ _ hπr, residueAt_apply]
  have : (-genDZ ^ 2 : Zs) = ⟨-11243, 7950⟩ := by decide
  rw [this]
  push_cast
  linear_combination (2809 : ZMod p) * hr

/-- **Multiples of `P₀` by multiples of the group order are formal.** -/
theorem zsmul_mem_W1_of_pointCount_dvd (hp2 : p ≠ 2) {r : ZMod p} (hr : r ^ 2 = 2)
    (h75 : (75 - 53 * r : ZMod p) ≠ 0) {π : Zs} (hπ : Prime π)
    (hπr : ∀ a, residueAt r hr a = 0 ↔ π ∣ a) {h : ℤ}
    (hd : (pointCount p (-(75 - 53 * r) ^ 2) : ℤ) ∣ h) :
    h • genP0 ∈ W1 (vP π hπ) (-genD ^ 2) := by
  have : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  have : (shortCurve (-(75 - 53 * r) ^ 2 : ZMod p)).IsElliptic :=
    shortCurve_isElliptic (neg_ne_zero.mpr (pow_ne_zero _ h75))
  set ρ := residueAt r hr
  have hA := vge_neg_genD_sq _ hπ
  have hAb := res_neg_genD_sq hr hπ hπr
  obtain ⟨k, rfl⟩ := hd
  let P0' : (shortCurve (-genD ^ 2)).toAffine.Point := genP0
  have hred : red hπ ρ hπr hA hAb ((↑(pointCount p (-(75 - 53 * r) ^ 2)) * k) • P0') = 0 := by
    rw [← redHom_apply, map_zsmul, mul_comm ((pointCount p (-(75 - 53 * r) ^ 2) : ℕ) : ℤ) k,
      ← smul_smul, natCast_zsmul, redHom_apply, ← card_point_shortCurve p,
      card_nsmul_eq_zero', smul_zero]
  suffices hW : ((↑(pointCount p (-(75 - 53 * r) ^ 2)) * k) • P0') ∈ W1 (vP π hπ) (-genD ^ 2) by
    exact hW
  generalize ((↑(pointCount p (-(75 - 53 * r) ^ 2)) * k) • P0') = Q at hred ⊢
  rcases Q with _ | ⟨x, y, hxy⟩
  · exact trivial
  · by_cases hx : VGe π 0 x
    · rw [red_some_of_vge hπ ρ hπr hA hAb hxy hx] at hred
      exact absurd hred (Point.some_ne_zero _)
    · show vP π hπ x < 0
      have hx0 : x ≠ 0 := fun h0 => hx (Or.inl h0)
      rw [vge_iff hx0] at hx
      rw [vP_apply hπ hx0]
      exact WithTop.coe_lt_coe.mpr (by omega)

/-- The residue map at the conjugate prime: `a + b s ↦ a - b r` has kernel `(σπ)`. -/
theorem residueAt_neg_ker {r : ZMod p} (hr : r ^ 2 = 2) {π : Zs}
    (hπr : ∀ a, residueAt r hr a = 0 ↔ π ∣ a) (hr' : (-r) ^ 2 = 2) :
    ∀ a, residueAt (-r) hr' a = 0 ↔ star π ∣ a := by
  intro a
  have e : residueAt (-r) hr' a = residueAt r hr (star a) := by
    simp [residueAt_apply]
  rw [e, hπr]
  have := star_pow_dvd_iff (π := π) (a := a) 1
  simp only [pow_one] at this
  exact this.symm

end ZInQ.Mult
