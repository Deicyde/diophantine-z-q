import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Grid
import ZInQKernel.Contrib.OneProof.RC.BlocksPerU.ThetaTransform
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-! Compose the two concrete generator calculations. The real factor of a word
is the same for every diagonal ternary form, so it cancels against the cube
of the ordinary theta series. At a cusp only its absolute value is needed. -/

noncomputable section

namespace ZInQ.Manuscript.RC.OldStageLaw

open Complex Matrix.SpecialLinearGroup CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped BigOperators MatrixGroups Real Manifold

/-- A generator in a word for `SL₂(ℤ)`. Inversion is used in the ambient
modular group; it need not belong to the old congruence subgroup. -/
inductive Step where
  | inv
  | trans (n : ℤ)

def Step.matrix : Step → SL(2, ℤ)
  | .inv => ModularGroup.S
  | .trans n => ModularGroup.T ^ n

def wordMatrix : List Step → SL(2, ℤ)
  | [] => 1
  | g :: gs => g.matrix * wordMatrix gs

def wordAction {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)] : List Step → (Grid a → ℂ) → Grid a → ℂ
  | [], w => w
  | .inv :: gs, w => wordAction gs (finiteFourier w)
  | .trans n :: gs, w => wordAction gs (twist n w)

def wordFactor : List Step → ℍ → ℂ
  | [], _ => 1
  | .inv :: gs, z => inversionFactor (wordMatrix gs • z : ℍ) * wordFactor gs z
  | .trans _ :: gs, z => wordFactor gs z

private theorem wordMatrix_append (g h : List Step) :
    wordMatrix (g ++ h) = wordMatrix g * wordMatrix h := by
  induction g with
  | nil => simp [wordMatrix]
  | cons s g ih => simp [wordMatrix, ih, mul_assoc]

private theorem exists_inverse_word (w : List Step) : ∃ v, wordMatrix v = (wordMatrix w)⁻¹ := by
  induction w with
  | nil => exact ⟨[], by simp [wordMatrix]⟩
  | cons s gs ih =>
    obtain ⟨v, hv⟩ := ih
    have hi : ∃ u : List Step, wordMatrix u = s.matrix⁻¹ := by
      cases s with
      | inv => exact ⟨[.inv, .inv, .inv], by decide⟩
      | trans n => exact ⟨[.trans (-n)], by simp [wordMatrix, Step.matrix]⟩
    obtain ⟨u, hu⟩ := hi
    exact ⟨v ++ u, by rw [wordMatrix_append, hv, hu, wordMatrix, mul_inv_rev]⟩

theorem exists_word (γ : SL(2, ℤ)) : ∃ w : List Step, wordMatrix w = γ := by
  have hg : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by simp [SpecialLinearGroup.SL2Z_generators]
  induction hg using Subgroup.closure_induction with
  | one => exact ⟨[], rfl⟩
  | mem g hg =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨[.inv], mul_one _⟩
    · exact ⟨[.trans 1], by simp [wordMatrix, Step.matrix]⟩
  | mul g h _ _ ig ih =>
    obtain ⟨w, rfl⟩ := ig
    obtain ⟨v, rfl⟩ := ih
    exact ⟨w ++ v, wordMatrix_append _ _⟩
  | inv g _ ig =>
    obtain ⟨w, rfl⟩ := ig
    exact exists_inverse_word w

variable {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)]

theorem gridTheta_word (ha : ∀ i, 0 < a i) (w : Grid a → ℂ) (l : List Step) (z : ℍ) :
    gridTheta w (wordMatrix l • z : ℍ) = wordFactor l z * gridTheta (wordAction l w) z := by
  induction l generalizing w with
  | nil => simp [wordMatrix, wordFactor, wordAction]
  | cons s gs ih =>
    cases s with
    | inv =>
      simp only [wordMatrix, Step.matrix, mul_smul, wordFactor, wordAction]
      rw [modular_S_smul, coe_mk, show ∀ v : ℂ, (-v)⁻¹ = -1 / v by simp [neg_div],
        gridTheta_inversion ha, ih, mul_assoc]
    | trans n =>
      simp only [wordMatrix, Step.matrix, mul_smul, wordFactor, wordAction]
      rw [modular_T_zpow_smul, coe_vadd]
      push_cast
      rw [add_comm]
      exact (gridTheta_translate ha w n (wordMatrix gs • z)).trans (ih _)

private theorem norm_inversionFactor (z : ℍ) :
    ‖inversionFactor z‖ = ‖(z : ℂ)‖ ^ (3 / 2 : ℝ) := by
  have h : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; rfl
  rw [inversionFactor, norm_pow, norm_div, norm_one, h, norm_cpow_real, norm_div, norm_I]
  simp only [one_div, Real.inv_rpow (norm_nonneg _), inv_inv]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  norm_num

theorem norm_wordFactor (l : List Step) (z : ℍ) :
    ‖wordFactor l z‖ = ‖denom (wordMatrix l) z‖ ^ (3 / 2 : ℝ) := by
  induction l with
  | nil => simp [wordFactor, wordMatrix]
  | cons s gs ih =>
    have hc : denom ((s.matrix * wordMatrix gs : SL(2, ℤ)) : GL (Fin 2) ℝ) z =
        denom s.matrix (wordMatrix gs • z : ℍ) * denom (wordMatrix gs) z := by
      change denom (mapGL ℝ (s.matrix * wordMatrix gs)) z = _
      rw [map_mul, denom_cocycle']
      have hp : 0 < (mapGL ℝ (wordMatrix gs)).det.val := by simp
      rw [σ, ite_eq_left hp]
      rfl
    have hD : ‖denom ((s.matrix * wordMatrix gs : SL(2, ℤ)) : GL (Fin 2) ℝ) z‖ ^ (3 / 2 : ℝ) =
        ‖denom s.matrix (wordMatrix gs • z : ℍ)‖ ^ (3 / 2 : ℝ) *
          ‖denom (wordMatrix gs) z‖ ^ (3 / 2 : ℝ) := by
      rw [hc, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    cases s with
    | inv => simpa only [wordMatrix, wordFactor, norm_mul, norm_inversionFactor, ih,
        Step.matrix, ModularGroup.denom_S] using hD.symm
    | trans n =>
      have ht : denom ((ModularGroup.T ^ n : SL(2, ℤ)) : GL (Fin 2) ℝ) (wordMatrix gs • z : ℍ) = 1 := by
        rw [ModularGroup.denom_apply (ModularGroup.T ^ n) (wordMatrix gs • z)]
        simp [ModularGroup.coe_T_zpow]
      simpa only [wordMatrix, wordFactor, ih, Step.matrix, ht, norm_one, Real.one_rpow,
        one_mul] using hD.symm

private theorem norm_kernel (z : ℍ) (t : ℝ) : ‖kernel z t‖ = Real.exp (-(2 * π * z.im * t)) := by
  rw [kernel, norm_exp]
  congr 1
  simp [mul_re, mul_im]

private theorem norm_line_le {b : ℝ} (hb : 0 < b) (r : ℝ) (z : ℍ) (hz : 1 ≤ z.im) :
    ‖line b r z‖ ≤ ∑' n : ℤ, ‖kernel (UpperHalfPlane.I : ℍ) (b * ((n : ℝ) + r)^2)‖ := by
  rw [← (line_hasSum hb r z).tsum_eq]
  refine (norm_tsum_le_tsum_norm (line_hasSum hb r z).summable.norm).trans
    ((line_hasSum hb r z).summable.norm.tsum_le_tsum ?_
      (line_hasSum hb r UpperHalfPlane.I).summable.norm)
  intro n
  rw [norm_kernel z, norm_kernel UpperHalfPlane.I, UpperHalfPlane.I_im, mul_one]
  apply Real.exp_le_exp.mpr
  have hq : 0 ≤ b * ((n : ℝ) + r) ^ 2 := by positivity
  nlinarith [mul_nonneg (mul_nonneg (by positivity : 0 ≤ 2 * π) (sub_nonneg.mpr hz)) hq]

theorem gridTheta_bounded (ha : ∀ i, 0 < a i) (w : Grid a → ℂ) :
    IsBoundedAtImInfty (fun z : ℍ => gridTheta w z) := by
  apply isBoundedAtImInfty_iff.mpr
  let B (r : Grid a) (i : Fin 3) : ℝ :=
    ∑' n : ℤ, ‖kernel (UpperHalfPlane.I : ℍ) (a i * ((n : ℝ) + offset r i)^2)‖
  refine ⟨∑ r, ‖w r‖ * ∏ i, B r i, 1, fun z hz => ?_⟩
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [norm_mul, norm_prod]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun i _ => norm_line_le (Nat.cast_pos.mpr (ha i)) _ z hz)) (norm_nonneg _)

theorem gridTheta_cusps (ha : ∀ i, 0 < a i) (w : Grid a → ℂ) (γ : SL(2, ℤ)) :
    IsBoundedAtImInfty (BlocksPerU.cuspNorm (3 / 2) (fun z => gridTheta w z) γ) := by
  obtain ⟨l, rfl⟩ := exists_word γ
  have he : BlocksPerU.cuspNorm (3 / 2) (fun z => gridTheta w z) (wordMatrix l) =
      (fun z : ℍ => ‖gridTheta (wordAction l w) z‖) := by
    funext z
    change ‖gridTheta w (wordMatrix l • z : ℍ)‖ * ‖denom (wordMatrix l) z‖ ^ (-(3 / 2) : ℝ) = _
    rw [gridTheta_word ha, norm_mul, norm_wordFactor]
    have h : 0 < ‖denom (wordMatrix l) z‖ := norm_pos_iff.mpr (denom_ne_zero _ _)
    rw [mul_right_comm, ← Real.rpow_add h, add_neg_cancel, Real.rpow_zero, one_mul]
  rw [he]; obtain ⟨M, A, h⟩ := isBoundedAtImInfty_iff.mp (gridTheta_bounded ha (wordAction l w))
  exact isBoundedAtImInfty_iff.mpr ⟨M, A, fun z hz => by simpa using h z hz⟩

#print axioms wordMatrix_append
#print axioms exists_inverse_word
#print axioms exists_word
#print axioms gridTheta_word
#print axioms norm_inversionFactor
#print axioms norm_wordFactor
#print axioms norm_kernel
#print axioms norm_line_le
#print axioms gridTheta_bounded
#print axioms gridTheta_cusps

end ZInQ.Manuscript.RC.OldStageLaw
