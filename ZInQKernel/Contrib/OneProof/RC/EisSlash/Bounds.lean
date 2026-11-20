import ZInQKernel.Contrib.OneProof.RC.EisSlash.Lattice
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-! Growth of the translated weight-two rows at infinity, via the
Lipschitz identity. The majorant is on-the-spot (c) for tex 9647–9654,
9762–9764 and 9862–9864. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EisSlash

open Matrix ModularForm UpperHalfPlane EisensteinSeries
open scoped MatrixGroups

private def rowKernel (N : ℕ) (k b : ℤ) (z : ℍ) : ℂ :=
  ∑' n : ℤ, eisSummand 2 ![k, (N : ℤ) * n + b] z

private theorem gridRow_eq_kernel (N : ℕ) (a : Fin 2 → ℤ) (z : ℍ) (m : ℤ) :
    gridRow N a z m = rowKernel N ((N : ℤ) * m + a 0) (a 1) z := rfl

private theorem rowKernel_neg (N : ℕ) (k b : ℤ) (z : ℍ) :
    rowKernel N (-k) (-b) z = rowKernel N k b z := by
  rw [rowKernel, rowKernel, ← tsum_comp_neg]
  apply tsum_congr
  intro n
  simp only [eisSummand, Fin.isValue, cons_val_zero, cons_val_one, Int.reduceNeg, Int.cast_neg,
    Int.mul_neg, ← neg_add, neg_mul]
  rw [_root_.zpow_neg, _root_.zpow_neg]
  simp [zpow_ofNat]
  ring

private theorem rowKernel_zero (N : ℕ) (b : ℤ) (z w : ℍ) :
    rowKernel N 0 b z = rowKernel N 0 b w := by
  simp [rowKernel, eisSummand]

private def positiveShift (N : ℕ) [NeZero N] (k b : ℤ) (hk : 0 < k) (z : ℍ) : ℍ :=
  ⟨((k : ℂ) * z + (b : ℂ)) / N, by
    rw [← Complex.ofReal_natCast, Complex.div_ofReal_im]
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_im, Complex.intCast_re,
      zero_mul, add_zero]
    exact div_pos (mul_pos (by exact_mod_cast hk) z.im_pos)
      (by exact_mod_cast NeZero.pos N)⟩

private theorem positiveShift_im (N : ℕ) [NeZero N] (k b : ℤ) (hk : 0 < k) (z : ℍ) :
    (positiveShift N k b hk z).im = (k : ℝ) * z.im / N := by
  change (((k : ℂ) * z + (b : ℂ)) / N).im = _
  rw [← Complex.ofReal_natCast, Complex.div_ofReal_im]
  simp

private def rowFactor (N : ℕ) : ℂ :=
  ((N : ℂ) ^ 2)⁻¹ * (-2 * Real.pi * Complex.I) ^ 2

private theorem rowKernel_fourier (N : ℕ) [NeZero N] (k b : ℤ) (hk : 0 < k) (z : ℍ) :
    rowKernel N k b z = rowFactor N *
      ∑' n : ℕ, (n : ℂ) * Function.Periodic.qParam 1 (positiveShift N k b hk z) ^ n := by
  have heq : rowKernel N k b z = ((N : ℂ) ^ 2)⁻¹ *
      ∑' n : ℤ, 1 / (((positiveShift N k b hk z : ℍ) : ℂ) + n) ^ 2 := by
    rw [rowKernel, ← tsum_mul_left]
    apply tsum_congr
    intro n
    simp only [eisSummand, Fin.isValue, cons_val_zero, cons_val_one, Int.reduceNeg,
      Int.cast_add, Int.cast_mul, Int.cast_natCast, _root_.zpow_neg, zpow_ofNat,
      positiveShift, one_div]
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
    have h : (k : ℂ) * z + ((N : ℂ) * n + b) =
        (N : ℂ) * ((((k : ℂ) * z + b) / N) + n) := by
      field_simp
      ring
    rw [h, mul_pow, mul_inv]
  rw [heq, qExpansion_identity (k := 1) (by decide), ← mul_assoc]
  simp [rowFactor, Function.Periodic.qParam]

private def decay (N : ℕ) (y : ℝ) : ℝ := Real.exp (-Real.pi * y / N)

private theorem decay_lt_one (N : ℕ) [NeZero N] {y : ℝ} (hy : 0 < y) :
    decay N y < 1 := by
  apply Real.exp_lt_one_iff.mpr
  exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) hy)
    (by exact_mod_cast NeZero.pos N)

private theorem summable_decay (N : ℕ) [NeZero N] {y : ℝ} (hy : 0 < y) :
    Summable fun n : ℕ => (n : ℝ) * (decay N y) ^ n := by
  have hr : 0 < decay N y := Real.exp_pos _
  simpa only [pow_one, Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr.le _))]
    using summable_norm_pow_mul_geometric_of_norm_lt_one 1
      (by rw [Real.norm_of_nonneg hr.le]; exact decay_lt_one N hy : ‖decay N y‖ < 1)

private theorem rowKernel_bound_pos (N : ℕ) [NeZero N] (k b : ℤ) (hk : 0 < k)
    (z : ℍ) {y : ℝ} (hy : 0 < y) (hzy : y ≤ z.im) :
    ‖rowKernel N k b z‖ ≤
      ‖rowFactor N‖ * (∑' n : ℕ, (n : ℝ) * (decay N y) ^ n) * (decay N y) ^ k.natAbs := by
  rw [rowKernel_fourier N k b hk, norm_mul, mul_assoc]
  gcongr
  let w := positiveShift N k b hk z
  have hS : Summable (fun n : ℕ => (n : ℂ) * Function.Periodic.qParam 1 w ^ n) := by
    simpa [Function.Periodic.qParam] using summable_pow_mul_cexp 1 1 w
  refine (norm_tsum_le_tsum_norm hS.norm).trans ?_
  rw [← tsum_mul_right]
  apply hS.norm.tsum_le_tsum _ ((summable_decay N hy).mul_right _)
  intro n
  rw [norm_mul, Complex.norm_natCast, norm_pow]
  by_cases hn : n = 0
  · simp [hn]
  have hq : ‖Function.Periodic.qParam 1 w‖ ≤ (decay N y) ^ (2 * k.natAbs) := by
    rw [Function.Periodic.norm_qParam, div_one, decay, ← Real.exp_nat_mul, Real.exp_le_exp]
    change -2 * Real.pi * (positiveShift N k b hk z).im ≤ _
    have hnat : (k.natAbs : ℝ) = (k : ℝ) := by
      rw [← Int.cast_natCast, Int.natAbs_of_nonneg hk.le]
    rw [positiveShift_im, Nat.cast_mul, Nat.cast_ofNat, hnat]
    have hN : 0 < (N : ℝ) := by exact_mod_cast NeZero.pos N
    field_simp
    have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
    nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hk'.le) (sub_nonneg.mpr hzy)]
  have hq' := pow_le_pow_left₀ (norm_nonneg _) hq n
  rw [← pow_mul] at hq'
  refine (mul_le_mul_of_nonneg_left hq' (Nat.cast_nonneg _)).trans ?_
  rw [mul_assoc (n : ℝ), ← pow_add]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply pow_le_pow_of_le_one (Real.exp_pos _).le (decay_lt_one N hy).le
  · have hk' := Int.natAbs_pos.mpr hk.ne'
    have h₁ : k.natAbs ≤ k.natAbs * n := by
      simpa using Nat.mul_le_mul_left k.natAbs (Nat.pos_of_ne_zero hn)
    have h₂ : n ≤ k.natAbs * n := by simpa using Nat.mul_le_mul_right n hk'
    rw [Nat.mul_assoc, two_mul]
    exact Nat.add_le_add h₂ h₁

private theorem gridRow_majorant (N : ℕ) [NeZero N] (a : Fin 2 → ℤ) {y : ℝ}
    (hy : 0 < y) :
    ∃ M : ℤ → ℝ, Summable M ∧ ∀ z : ℍ, y ≤ z.im → ∀ m, ‖gridRow N a z m‖ ≤ M m := by
  let w : ℍ := ⟨Complex.I, by simp⟩
  let A := ‖rowKernel N 0 (a 1) w‖
  let B := ‖rowFactor N‖ * ∑' n : ℕ, (n : ℝ) * (decay N y) ^ n
  have hB : 0 ≤ B := mul_nonneg (norm_nonneg _) (tsum_nonneg fun _ => by
    exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Real.exp_pos _).le _))
  let F (k : ℤ) : ℝ := (A + B) * (decay N y) ^ k.natAbs
  let e (m : ℤ) := (N : ℤ) * m + a 0
  have hF : Summable F := by
    change Summable (fun k : ℤ => (A + B) * decay N y ^ k.natAbs)
    apply Summable.mul_left
    rw [summable_int_iff_summable_nat_and_neg]
    have hs := summable_geometric_of_lt_one (show 0 ≤ decay N y from (Real.exp_pos _).le)
      (decay_lt_one N hy)
    simpa only [Int.natAbs_natCast, Int.natAbs_neg] using And.intro hs hs
  have he : Function.Injective e := by
    intro m n h
    apply mul_left_cancel₀ (a := (N : ℤ)) (by exact_mod_cast NeZero.ne N)
    exact add_right_cancel h
  refine ⟨F ∘ e, hF.comp_injective he, ?_⟩
  intro z hz m
  rw [gridRow_eq_kernel]
  change ‖rowKernel N (e m) (a 1) z‖ ≤ F (e m)
  rcases lt_trichotomy 0 (e m) with hk | hk | hk
  · exact (rowKernel_bound_pos N _ _ hk z hy hz).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (norm_nonneg _)) (pow_nonneg (Real.exp_pos _).le _))
  · rw [← hk, rowKernel_zero N _ z w]
    simpa [F, A] using (le_add_of_nonneg_right hB : A ≤ A + B)
  · rw [← rowKernel_neg N (e m) (a 1) z]
    have hb := rowKernel_bound_pos N (-e m) (-a 1) (by omega) z hy hz
    rw [Int.natAbs_neg] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (norm_nonneg _))
      (pow_nonneg (Real.exp_pos _).le _))

/-- The outer sums of the iterated residue-class rows converge. -/
theorem summable_gridRows (N : ℕ) [NeZero N] (a : Fin 2 → ℤ) (z : ℍ) :
    Summable (gridRow N a z) := by
  obtain ⟨M, hM, h⟩ := gridRow_majorant N a z.im_pos
  exact hM.of_norm_bounded (h z le_rfl)

/-- Each iterated residue-class sum is bounded at the cusp at infinity. -/
theorem gridSeries_bounded (N : ℕ) [NeZero N] (a : Fin 2 → ℤ) :
    IsBoundedAtImInfty (gridSeries N a) := by
  obtain ⟨M, hM, h⟩ := gridRow_majorant N a zero_lt_one
  exact isBoundedAtImInfty_iff.mpr ⟨∑' m, M m, 1, fun z hz =>
    (norm_tsum_le_tsum_norm (summable_gridRows N a z).norm).trans
      ((summable_gridRows N a z).norm.tsum_le_tsum (h z hz) hM)⟩

theorem latticeDiff_eq_gridSeries_sub (N : ℕ) [NeZero N] (a b : Fin 2 → ℤ) :
    latticeDiff N a b = gridSeries N a - gridSeries N b := by
  funext z
  exact (latticeDiff_eq_rows N a b z).trans
    ((summable_gridRows N a z).tsum_sub (summable_gridRows N b z))

theorem latticeDiff_shift (N : ℕ) [NeZero N] (a b r s : Fin 2 → ℤ) :
    latticeDiff N (grid N a r) (grid N b s) = latticeDiff N a b := by
  simp only [latticeDiff_eq_gridSeries_sub, gridSeries_shift]


end ZInQ.Manuscript.RC.EisSlash
