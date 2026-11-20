import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable

/-! Absolute convergence after subtracting two translates of the weight-two
lattice kernel. This regularization is on-the-spot (c) for the character pairs
used at tex 9647–9654, 9762–9764 and 9862–9864. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EisSlash

open Matrix Matrix.SpecialLinearGroup ModularForm UpperHalfPlane EisensteinSeries
open Filter Asymptotics
open scoped MatrixGroups Real

private def linear (z : ℍ) (x : Fin 2 → ℤ) : ℂ := x 0 * (z : ℂ) + x 1

private theorem linear_eq_zero_iff (z : ℍ) (x : Fin 2 → ℤ) :
    linear z x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h0 := congrArg Complex.im h
    simp only [linear, Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
      zero_mul, add_zero, Complex.zero_im, mul_eq_zero] at h0
    have h0' : x 0 = 0 := by exact_mod_cast h0.resolve_right z.im_ne_zero
    simp [linear, h0'] at h
    funext i
    fin_cases i
    · exact h0'
    · exact h
  · rintro rfl
    simp [linear]

private theorem summand_eq (z : ℍ) (x : Fin 2 → ℤ) :
    eisSummand 2 x z = (linear z x)⁻¹ * (linear z x)⁻¹ := by
  simp [eisSummand, linear, _root_.zpow_neg, pow_two]

/-- Integral lattice points of a fixed residue class. -/
def grid (N : ℕ) (a x : Fin 2 → ℤ) : Fin 2 → ℤ := (N : ℤ) • x + a

private theorem grid_injective (N : ℕ) [NeZero N] (a : Fin 2 → ℤ) :
    Function.Injective (grid N a) := by
  intro x y h
  funext i
  have hi := congrFun h i
  change (N : ℤ) * x i + a i = (N : ℤ) * y i + a i at hi
  exact mul_left_cancel₀ (by exact_mod_cast NeZero.ne N) (add_right_cancel hi)

private theorem linear_grid_bigO (z : ℍ) (N : ℕ) [NeZero N] (a : Fin 2 → ℤ) :
    (fun x => (linear z (grid N a x))⁻¹) =O[cofinite] (fun x => ‖x‖⁻¹) := by
  have h := isBigO_linear_add_const_vec z 0 0
  have h' : (fun x : Fin 2 → ℤ => (linear z x)⁻¹) =O[cofinite] (fun x => ‖x‖⁻¹) := by
    simpa [linear] using h
  have hg := grid_injective N a
  have hc : Tendsto (grid N a) cofinite cofinite := hg.tendsto_cofinite
  have he : (fun x => ‖grid N a x‖⁻¹) =Θ[cofinite] (fun x => ‖x‖⁻¹) := by
    have hn (x : Fin 2 → ℤ) : ‖(N : ℤ) • x‖ = (N : ℝ) * ‖x‖ := by
      rw [norm_eq_max_natAbs, norm_eq_max_natAbs]
      change ((max ((N : ℤ) * x 0).natAbs ((N : ℤ) * x 1).natAbs : ℕ) : ℝ) = _
      simp only [Int.natAbs_mul, Int.natAbs_natCast, Nat.cast_max, Nat.cast_mul]
      exact (mul_max_of_nonneg _ _ (by positivity)).symm
    have hk : (fun x : Fin 2 → ℤ => (N : ℤ) • x) =Θ[cofinite] (id : (Fin 2 → ℤ) → _) := by
      rw [← isTheta_norm_left, ← isTheta_norm_right]
      simpa only [hn, id_eq] using
        (isTheta_refl (fun x : Fin 2 → ℤ => ‖x‖) cofinite).const_mul_left
          (show (N : ℝ) ≠ 0 by exact_mod_cast NeZero.ne N)
    have hsmall : (fun _ : Fin 2 → ℤ => a) =o[cofinite] id :=
      isLittleO_norm_right.mp (isLittleO_const_left_of_properSpace_of_discreteTopology a)
    have ht : grid N a =Θ[cofinite] id := hk.add_isLittleO hsmall
    exact isTheta_inv.mpr ht.norm_left.norm_right
  exact (h'.comp_tendsto hc).trans he.isBigO

/-- The two shifted terms may be subtracted before summing in any order. -/
theorem summable_lattice_diff (z : ℍ) (N : ℕ) [NeZero N] (a b : Fin 2 → ℤ) :
    Summable fun x : Fin 2 → ℤ => eisSummand 2 (grid N a x) z - eisSummand 2 (grid N b x) z := by
  let A (x : Fin 2 → ℤ) : ℂ := (linear z (grid N a x))⁻¹
  let B (x : Fin 2 → ℤ) : ℂ := (linear z (grid N b x))⁻¹
  have hA : A =O[cofinite] (fun x => ‖x‖⁻¹) := linear_grid_bigO z N a
  have hB : B =O[cofinite] (fun x => ‖x‖⁻¹) := linear_grid_bigO z N b
  let c := linear z (b - a)
  have hS : Summable (fun x => c * (A x * B x * (A x + B x))) := by
    apply summable_of_isBigO_rpow_norm (a := 3) (by norm_num)
    have hr (x : ℝ) : x⁻¹ * x⁻¹ * x⁻¹ = (x ^ (3 : ℕ))⁻¹ := by
      rw [← mul_inv, ← mul_inv, pow_succ, pow_two]
    have hx (x : ℝ) : x ^ (3 : ℝ) = x ^ (3 : ℕ) := by norm_cast
    simpa only [← mul_assoc, hr, hx] using
      ((hA.mul hB).mul (hA.add hB)).const_mul_left c
  apply hS.congr_cofinite
  have ev (d : Fin 2 → ℤ) : ∀ᶠ x in cofinite, grid N d x ≠ 0 :=
    (grid_injective N d).tendsto_cofinite.eventually (eventually_cofinite_ne 0)
  filter_upwards [ev a, ev b] with x hxa hxb
  have ha : linear z (grid N a x) ≠ 0 := mt (linear_eq_zero_iff z _).mp hxa
  have hb : linear z (grid N b x) ≠ 0 := mt (linear_eq_zero_iff z _).mp hxb
  have h : c = linear z (grid N b x) - linear z (grid N a x) := by
    simp [c, linear, grid, Int.cast_add, Int.cast_sub]
    ring
  rw [h, summand_eq, summand_eq]
  dsimp [A, B]
  field_simp
  ring

/-- The absolutely convergent difference of two translated lattices. -/
def latticeDiff (N : ℕ) (a b : Fin 2 → ℤ) : ℍ → ℂ :=
  fun z => ∑' x : (Fin 2 → ℤ), (eisSummand 2 (grid N a x) z - eisSummand 2 (grid N b x) z)

theorem latticeDiff_add (N : ℕ) [NeZero N] (a b c : Fin 2 → ℤ) :
    latticeDiff N a b + latticeDiff N b c = latticeDiff N a c := by
  ext z
  change (_ + _ : ℂ) = _
  rw [latticeDiff, latticeDiff, ← (summable_lattice_diff z N a b).tsum_add
    (summable_lattice_diff z N b c)]
  exact tsum_congr fun x => sub_add_sub_cancel _ _ _

private def rowEquiv (g : SL(2, ℤ)) : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) where
  toFun x := x ᵥ* g.val
  invFun x := x ᵥ* g⁻¹.val
  left_inv x := by
    change x ᵥ* g.val ᵥ* g⁻¹.val = x
    rw [vecMul_vecMul]
    have h := congrArg (fun a : SL(2, ℤ) => a.val) (mul_inv_cancel g)
    change g.val * g⁻¹.val = 1 at h
    rw [h, vecMul_one]
  right_inv x := by
    change x ᵥ* g⁻¹.val ᵥ* g.val = x
    rw [vecMul_vecMul]
    have h := congrArg (fun a : SL(2, ℤ) => a.val) (inv_mul_cancel g)
    change g⁻¹.val * g.val = 1 at h
    rw [h, vecMul_one]

/-- Slashing a lattice difference acts on its two row offsets. -/
theorem latticeDiff_slash (N : ℕ) (a b : Fin 2 → ℤ) (g : SL(2, ℤ)) :
    latticeDiff N a b ∣[(2 : ℤ)] g = latticeDiff N (a ᵥ* g.val) (b ᵥ* g.val) := by
  ext z
  rw [SL_slash_apply]
  simp only [latticeDiff, eisSummand_SL2_apply, ← mul_sub, tsum_mul_left]
  have hg (c x : Fin 2 → ℤ) : grid N c x ᵥ* g.val = grid N (c ᵥ* g.val) (rowEquiv g x) := by
    change (((N : ℤ) • x + c) ᵥ* g.val) = (N : ℤ) • (x ᵥ* g.val) + (c ᵥ* g.val)
    rw [add_vecMul, smul_vecMul]
  simp only [hg]
  rw [mul_comm (_ ^ (2 : ℤ)), mul_assoc, ← zpow_add₀ (denom_ne_zero g z)]
  simp only [add_neg_cancel, zpow_zero, mul_one]
  exact (rowEquiv g).tsum_eq (fun x => eisSummand 2 (grid N (a ᵥ* g.val) x) z -
    eisSummand 2 (grid N (b ᵥ* g.val) x) z)

/-- The inner lattice row with first index fixed. -/
def gridRow (N : ℕ) (a : Fin 2 → ℤ) (z : ℍ) (m : ℤ) : ℂ :=
  ∑' n : ℤ, eisSummand 2 (grid N a ![m, n]) z

theorem summable_gridRow_inner (N : ℕ) [NeZero N] (a : Fin 2 → ℤ) (z : ℍ) (m : ℤ) :
    Summable (fun n : ℤ => eisSummand 2 (grid N a ![m, n]) z) := by
  have hi : Function.Injective (fun n : ℤ => (N : ℤ) * n + a 1) := by
    intro x y h
    exact mul_left_cancel₀ (by exact_mod_cast NeZero.ne N) (add_right_cancel h)
  apply ((e2Summand_summable ((N : ℤ) * m + a 0) z).comp_injective hi).congr
  intro n
  rfl

private theorem summable_gridDiff_prod (N : ℕ) [NeZero N] (a b : Fin 2 → ℤ) (z : ℍ) :
    Summable fun x : ℤ × ℤ =>
      eisSummand 2 (grid N a ![x.1, x.2]) z - eisSummand 2 (grid N b ![x.1, x.2]) z :=
  (finTwoArrowEquiv _).symm.summable_iff.mpr (summable_lattice_diff z N a b)

/-- The difference can also be evaluated by summing the differences of rows. -/
theorem latticeDiff_eq_rows (N : ℕ) [NeZero N] (a b : Fin 2 → ℤ) (z : ℍ) :
    latticeDiff N a b z = ∑' m : ℤ, (gridRow N a z m - gridRow N b z m) := by
  have hs := summable_gridDiff_prod N a b z
  rw [latticeDiff, ← (finTwoArrowEquiv ℤ).symm.tsum_eq]
  simp only [finTwoArrowEquiv_symm_apply]
  rw [hs.tsum_prod']
  · refine tsum_congr fun m => ?_
    exact (summable_gridRow_inner N a z m).tsum_sub (summable_gridRow_inner N b z m)
  · exact hs.prod_factor

/-- The residue class sum uses the indicated order of summation. -/
def gridSeries (N : ℕ) (a : Fin 2 → ℤ) : ℍ → ℂ :=
  fun z => ∑' m : ℤ, gridRow N a z m

theorem gridSeries_shift (N : ℕ) (a t : Fin 2 → ℤ) :
    gridSeries N (grid N a t) = gridSeries N a := by
  funext z
  calc
    _ = ∑' m : ℤ, gridRow N a z (m + t 0) := by
      refine tsum_congr fun m => ?_
      calc
        _ = ∑' n : ℤ, eisSummand 2 (grid N a ![m + t 0, n + t 1]) z := by
          refine tsum_congr fun n => ?_
          apply congrArg (fun v => eisSummand 2 v z)
          funext i
          fin_cases i
          · change (N : ℤ) * m + ((N : ℤ) * t 0 + a 0) = (N : ℤ) * (m + t 0) + a 0
            ring
          · change (N : ℤ) * n + ((N : ℤ) * t 1 + a 1) = (N : ℤ) * (n + t 1) + a 1
            ring
        _ = gridRow N a z (m + t 0) := (Equiv.addRight (t 1)).tsum_eq (fun n => eisSummand 2 (grid N a ![m + t 0, n]) z)
    _ = _ := (Equiv.addRight (t 0)).tsum_eq (gridRow N a z)


end ZInQ.Manuscript.RC.EisSlash
