import ZInQKernel.Multiplication.Completeness.SelectedReduction
import ZInQKernel.Multiplication.Local.Ratio
import ZInQKernel.Multiplication.Local.TruncationError
import ZInQKernel.Multiplication.Soundness.TestsToCongruence

/-!
# Precision of the tests at a selected prime

Blueprint: `multiplication/completeness/selected-prime-precision.md`.

Let `p > 324` be prime, `r² = 2` in `𝔽_p` with `75 ∓ 53 r ≠ 0`, `π` a prime of `ℤ[s]` with
`(π) = ker(a + b s ↦ a + b r)` (so `σπ` is the prime `(p, s + r)`), and `d₁, d₂` the orders of the
two reduced curves (`pointCount`). If `d₁ ∣ h` and `d₂ ∣ h - c_*`, then `H = [h]P₀` is formal at
`π` and `V₀ = [h - c_*]P₀` at `σπ`; by the formal logarithm and the truncation error,
`A_i ≡ n_i` and `σ B_i ≡ n_i` modulo `π^28`, so the eight inverse abscissas have valuation `≥ 1`
and the four `L`-tests valuation `≥ 28` at `π`.
-/

namespace ZInQ.Mult

open WeierstrassCurve WeierstrassCurve.Affine

section Completion

variable {π : Zs} (hπ : Prime π)

theorem zCoord_mapE (Q : genCurve.toAffine.Point) :
    zCoord (mapE π hπ Q) = algebraMap K0 ((primeSpec π hπ).adicCompletion K0) (zOf Q) := by
  rcases Q with _ | ⟨x, y, h⟩
  · show zCoord (0 : (shortCurve (-genDAt π hπ ^ 2)).toAffine.Point) = algebraMap K0 _ 0
    simp
  · show -(algebraMap K0 _ x) / (algebraMap K0 _ y) = algebraMap K0 _ (-x / y)
    simp [map_div₀]

theorem map_Lam (Q : genCurve.toAffine.Point) :
    algebraMap K0 ((primeSpec π hπ).adicCompletion K0) (Lam Q) =
      truncLog (genDAt π hπ ^ 2) (zCoord (mapE π hπ Q)) := by
  rw [Lam, map_truncLog, zCoord_mapE, map_pow]

end Completion

/-- **The `L`-ratio at a large prime.** If `p > 324`, `π ∣ p`, `h ≠ 0` and `[h]P₀` is formal at
`π`, then `Λ([nh]P₀)/Λ([h]P₀) ≡ n` modulo `π^28`. -/
theorem vge_Lam_ratio_sub {p : ℕ} [Fact p.Prime] (hp324 : 324 < p) {π : Zs} (hπ : Prime π)
    (hπp : π ∣ (p : Zs)) {h : ℤ} (h0 : h ≠ 0) (hH : h • genP0 ∈ W1 (vP π hπ) (-genD ^ 2))
    (n : ℤ) : Vge (vP π hπ) 28 (Lam ((n * h) • genP0) / Lam (h • genP0) - n) := by
  by_cases hn : n = 0
  · subst hn; simpa using Vge.zero (v := vP π hπ) 28
  set f := algebraMap K0 ((primeSpec π hπ).adicCompletion K0)
  have hU : (n * h) • genP0 ∈ W1 (vP π hπ) (-genD ^ 2) := by
    rw [← smul_smul]
    exact (zsmul_mem_W1 (vP_neg_genD_sq_nonneg hπ) hH n).1
  have hH' := mapE_mem_W1_of_mem hπ hH
  have hU' := mapE_mem_W1_of_mem hπ hU
  have hH0 := mapE_ne_zero hπ (zsmul_genP0_ne_zero h0)
  have hU0 := mapE_ne_zero hπ (zsmul_genP0_ne_zero (mul_ne_zero hn h0))
  obtain ⟨-, -, εH, hεH, hLH⟩ := log25_truncation_error hp324 hπ hπp _ hH' hH0
  obtain ⟨-, -, εU, hεU, hLU⟩ := log25_truncation_error hp324 hπ hπp _ hU' hU0
  obtain ⟨hl0, hratio⟩ := ellLog_ratio (p := p) (by omega) hπ hπp (u := n * h) h0 hH' hU'
  have hh : (h : (primeSpec π hπ).adicCompletion K0) ≠ 0 := Int.cast_ne_zero.mpr h0
  have hq : ((n * h : ℤ) : (primeSpec π hπ).adicCompletion K0) / (h : _) = n := by
    push_cast; field_simp
  rw [hq] at hratio
  have h1εH : (1 + εH) ≠ 0 := one_add_ne_zero (le_trans (by norm_num) hεH)
  have hvεH : vComp π hπ (1 + εH) = 0 := val_one_add (le_trans (by norm_num) hεH)
  have key : f (Lam ((n * h) • genP0) / Lam (h • genP0) - n) =
      (n : (primeSpec π hπ).adicCompletion K0) * (εU - εH) / (1 + εH) := by
    rw [map_sub, map_div₀, map_Lam, map_Lam, hLH, hLU, hratio, map_intCast]
    field_simp
    ring
  rw [Vge, ← vComp_algebraMap hπ, key]
  have hn' : Vge (vComp π hπ) 0 ((n : (primeSpec π hπ).adicCompletion K0)) := vge_intCast n
  have hεU' : Vge (vComp π hπ) 28 εU := by unfold Vge; exact_mod_cast hεU
  have hεH' : Vge (vComp π hπ) 28 εH := by unfold Vge; exact_mod_cast hεH
  have := (hn'.mul (hεU'.sub hεH')).div_unit hvεH
  rw [zero_add] at this
  exact this

/-- **Precision of the tests at a selected prime.** -/
theorem tests_precision_selected {p : ℕ} [Fact p.Prime] (hp324 : 324 < p) {r : ZMod p}
    (hr : r ^ 2 = 2) (h75 : (75 - 53 * r : ZMod p) ≠ 0) (h75' : (75 + 53 * r : ZMod p) ≠ 0)
    {π : Zs} (hπ : Prime π) (hπr : ∀ a, residueAt r hr a = 0 ↔ π ∣ a) {h : ℤ} (h0 : h ≠ 0)
    (hc : h ≠ Syntax.cstar) (hd₁ : (pointCount p (-(75 - 53 * r) ^ 2) : ℤ) ∣ h)
    (hd₂ : (pointCount p (-(75 + 53 * r) ^ 2) : ℤ) ∣ h - Syntax.cstar) (n₁ n₂ : ℤ) (j : Fin 12) :
    Vge (vP π hπ) (if j.val < 8 then 1 else 28)
      (testValues h ![n₁ * h, n₂ * h, n₁ * n₂ * h] (certShifts ![n₁, n₂, n₁ * n₂]) j) := by
  have hp2 : p ≠ 2 := by omega
  have hπp : π ∣ (p : Zs) := (hπr p).mp (by simp)
  have hr' : (-r) ^ 2 = 2 := by rw [neg_sq]; exact hr
  have hσr := residueAt_neg_ker hr hπr hr'
  have hσp : star π ∣ (p : Zs) := star_dvd_natCast hπp
  set h' : ℤ := h - Syntax.cstar with hh'
  have h'0 : h' ≠ 0 := sub_ne_zero.mpr hc
  -- `H` is formal at `π`, `V₀` at `σπ`
  have hH : h • genP0 ∈ W1 (vP π hπ) (-genD ^ 2) :=
    zsmul_mem_W1_of_pointCount_dvd hp2 hr h75 hπ hπr hd₁
  have hV : h' • genP0 ∈ W1 (vP (star π) (prime_star hπ)) (-genD ^ 2) := by
    refine zsmul_mem_W1_of_pointCount_dvd hp2 hr' (by rw [mul_neg, sub_neg_eq_add]; exact h75')
      (prime_star hπ) hσr ?_
    rw [mul_neg, sub_neg_eq_add]; exact hd₂
  have hA := vP_neg_genD_sq_nonneg hπ
  have hA' := vP_neg_genD_sq_nonneg (prime_star hπ)
  have hstar : ∀ (m : ℤ) (y : K0), Vge (vP (star π) (prime_star hπ)) m y →
      Vge (vP π hπ) m (star y) := by
    intro m y hy; rw [Vge, ← vP_star]; exact hy
  -- the shapes of the test points
  have hc0 : certShifts ![n₁, n₂, n₁ * n₂] 0 = Syntax.cstar := rfl
  have hz : ∀ (m : ℤ), (m * h) • genP0 = m • (h • genP0) := fun m => by rw [smul_smul]
  have hzc : ∀ m : ℤ, (m * h - Syntax.cstar * m) • genP0 = (m * h') • genP0 := fun m => by
    congr 1; rw [hh']; ring
  have hinv : ∀ m : ℤ, Vge (vP π hπ) 1 (invX ((m * h) • genP0)) := fun m => by
    rw [hz]; exact (vge_invX_of_W1 hπ (zsmul_mem_W1 hA hH m).1).mono (by norm_num)
  have hinv' : ∀ m : ℤ, Vge (vP π hπ) 1 (star (invX ((m * h') • genP0))) := fun m => by
    rw [← smul_smul]
    exact hstar _ _ ((vge_invX_of_W1 (prime_star hπ) (zsmul_mem_W1 hA' hV m).1).mono
      (by norm_num))
  have hAi : ∀ m : ℤ, Vge (vP π hπ) 28 (Lam ((m * h) • genP0) / Lam (h • genP0) - m) :=
    fun m => vge_Lam_ratio_sub hp324 hπ hπp h0 hH m
  have hBi : ∀ m : ℤ, Vge (vP π hπ) 28
      (star (Lam ((m * h') • genP0) / Lam (h' • genP0)) - m) := fun m => by
    have := hstar _ _ (vge_Lam_ratio_sub hp324 (prime_star hπ) hσp h'0 hV m)
    rwa [star_sub, show star (m : K0) = m by ext <;> simp] at this
  have htest : ∀ m : ℤ, Vge (vP π hπ) 28
      (Lam ((m * h) • genP0) / Lam (h • genP0) - star (Lam ((m * h') • genP0) / Lam (h' • genP0))) :=
    fun m => by
      have := (hAi m).sub (hBi m)
      rwa [sub_sub_sub_cancel_right] at this
  rw [testValues_eq]
  fin_cases j
  · simpa using (vge_invX_of_W1 hπ hH).mono (by norm_num)
  · simpa using hinv n₁
  · simpa using hinv n₂
  · simpa using hinv (n₁ * n₂)
  · simpa [hc0] using hstar _ _ ((vge_invX_of_W1 (prime_star hπ) hV).mono (by norm_num))
  · simpa [certShifts, hzc] using hinv' n₁
  · simpa [certShifts, hzc] using hinv' n₂
  · simpa [certShifts, hzc] using hinv' (n₁ * n₂)
  · simpa [certShifts, hzc] using htest n₁
  · simpa [certShifts, hzc] using htest n₂
  · simpa [certShifts, hzc] using htest (n₁ * n₂)
  · -- `A₁A₂ - A₃ ≡ n₁n₂ - n₁n₂`
    have e : ∀ a₁ a₂ a₃ : K0, a₁ * a₂ - a₃ = (a₁ - n₁) * (a₂ - n₂) + (n₁ : K0) * (a₂ - n₂) +
        (n₂ : K0) * (a₁ - n₁) - (a₃ - ((n₁ * n₂ : ℤ) : K0)) := by
      intro a₁ a₂ a₃; push_cast; ring
    simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    show Vge _ (28 : ℤ) _
    rw [e]
    refine ((((hAi n₁).mul (hAi n₂)).mono (by norm_num)).add
      (((vge_intCast n₁).mul (hAi n₂)).mono (by norm_num))).add
      (((vge_intCast n₂).mul (hAi n₁)).mono (by norm_num)) |>.sub (hAi (n₁ * n₂))

end ZInQ.Mult
