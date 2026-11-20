import ZInQKernel.Contrib.OneProof.RC.EisSlash.Bounds

/-! The finite residue-class representation in weight two, on-the-spot (c)
for the Eisenstein constituents of tex 9647–9654, 9762–9764 and 9862–9864. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EisSlash

open Matrix Matrix.SpecialLinearGroup ModularForm UpperHalfPlane
open scoped MatrixGroups

/-- Choose the standard representatives for a lattice vector modulo the level. -/
def residueLift {N : ℕ} (a : Fin 2 → ZMod N) : Fin 2 → ℤ := fun i => (a i).val

/-- Reduce the two lattice coordinates modulo the level. -/
def rowResidue (N : ℕ) (x : Fin 2 → ℤ) : Fin 2 → ZMod N := fun i => x i

@[simp] theorem rowResidue_lift {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) :
    rowResidue N (residueLift a) = a := by
  funext i
  simp [rowResidue, residueLift]

theorem exists_grid_of_residue_eq {N : ℕ} {v a : Fin 2 → ℤ}
    (h : rowResidue N v = rowResidue N a) : ∃ t, v = grid N a t := by
  have h' (i : Fin 2) : (N : ℤ) ∣ v i - a i := by
    have hi := congrFun h i
    change ((v i : ℤ) : ZMod N) = (a i : ZMod N) at hi
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, hi, sub_self]
  choose t ht using h'
  refine ⟨t, funext fun i => ?_⟩
  change v i = (N : ℤ) * t i + a i
  exact sub_eq_iff_eq_add.mp (ht i)

theorem rowResidue_vecMul (N : ℕ) (v : Fin 2 → ℤ) (g : SL(2, ℤ)) :
    rowResidue N (v ᵥ* g.val) = rowResidue N v ᵥ* (g.val.map (Int.castRingHom (ZMod N))) := by
  funext i
  simp [rowResidue, Matrix.vecMul, dotProduct, Int.cast_mul]

/-- The permutation of residue classes induced by the right action on rows. -/
def residueEquiv (N : ℕ) (g : SL(2, ℤ)) : (Fin 2 → ZMod N) ≃ (Fin 2 → ZMod N) where
  toFun a := a ᵥ* (g.val.map (Int.castRingHom (ZMod N)))
  invFun a := a ᵥ* (g⁻¹.val.map (Int.castRingHom (ZMod N)))
  left_inv a := by
    change (a ᵥ* g.val.map (Int.castRingHom (ZMod N))) ᵥ*
      g⁻¹.val.map (Int.castRingHom (ZMod N)) = a
    rw [vecMul_vecMul, ← Matrix.map_mul]
    have h := congrArg (fun m : SL(2, ℤ) => m.val) (mul_inv_cancel g)
    change g.val * g⁻¹.val = 1 at h
    rw [h, Matrix.map_one (f := Int.castRingHom (ZMod N)) (map_zero _) (map_one _), vecMul_one]
  right_inv a := by
    change (a ᵥ* g⁻¹.val.map (Int.castRingHom (ZMod N))) ᵥ*
      g.val.map (Int.castRingHom (ZMod N)) = a
    rw [vecMul_vecMul, ← Matrix.map_mul]
    have h := congrArg (fun m : SL(2, ℤ) => m.val) (inv_mul_cancel g)
    change g⁻¹.val * g.val = 1 at h
    rw [h, Matrix.map_one (f := Int.castRingHom (ZMod N)) (map_zero _) (map_one _), vecMul_one]

/-- Finite weighted sum of the absolutely convergent lattice differences
with reference residue zero. -/
def gridCombination (N : ℕ) [NeZero N] (w : (Fin 2 → ZMod N) → ℂ) : ℍ → ℂ :=
  fun z => ∑ a : Fin 2 → ZMod N, w a * latticeDiff N (residueLift a) 0 z

/-- For zero total weight the subtraction of the common reference cancels. -/
theorem gridCombination_eq_rows (N : ℕ) [NeZero N] (w : (Fin 2 → ZMod N) → ℂ)
    (hw : ∑ a, w a = 0) (z : ℍ) :
    gridCombination N w z = ∑ a, w a * gridSeries N (residueLift a) z := by
  simp only [gridCombination, latticeDiff_eq_gridSeries_sub, Pi.sub_apply, mul_sub,
    Finset.sum_sub_distrib, ← Finset.sum_mul, hw, zero_mul, sub_zero]

private theorem latticeDiff_residue_slash (N : ℕ) [NeZero N] (a : Fin 2 → ZMod N)
    (g : SL(2, ℤ)) :
    latticeDiff N (residueLift a) 0 ∣[(2 : ℤ)] g =
      latticeDiff N (residueLift (residueEquiv N g a)) 0 := by
  rw [latticeDiff_slash, zero_vecMul]
  obtain ⟨t, ht⟩ := exists_grid_of_residue_eq
    (v := residueLift a ᵥ* g.val) (a := residueLift (residueEquiv N g a))
    (by rw [rowResidue_vecMul, rowResidue_lift, rowResidue_lift]; rfl)
  rw [ht]
  have hz : grid N 0 0 = 0 := by simp [grid]
  simpa only [hz] using (latticeDiff_shift N (residueLift (residueEquiv N g a)) 0 t 0)

/-- Weight-two slash permutes the residue classes and pulls the weights back. -/
theorem gridCombination_slash (N : ℕ) [NeZero N] (w : (Fin 2 → ZMod N) → ℂ)
    (g : SL(2, ℤ)) :
    gridCombination N w ∣[(2 : ℤ)] g = gridCombination N (w ∘ (residueEquiv N g).symm) := by
  funext z
  calc
    _ = ∑ a : Fin 2 → ZMod N, w a *
        (latticeDiff N (residueLift a) 0 ∣[(2 : ℤ)] g) z := by
      simp only [SL_slash_apply, gridCombination, Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ = ∑ a : Fin 2 → ZMod N, w a *
        latticeDiff N (residueLift (residueEquiv N g a)) 0 z := by
      simp only [latticeDiff_residue_slash]
    _ = _ := by
      simpa only [gridCombination, Function.comp_apply, Equiv.symm_apply_apply] using
        (residueEquiv N g).sum_comp
          (fun a => w ((residueEquiv N g).symm a) * latticeDiff N (residueLift a) 0 z)

/-- If the weights transform by a scalar, so does their weighted form. -/
theorem gridCombination_slash_scalar (N : ℕ) [NeZero N] (w : (Fin 2 → ZMod N) → ℂ)
    (g : SL(2, ℤ)) (s : ℂ) (hw : ∀ a, w ((residueEquiv N g).symm a) = s * w a) :
    gridCombination N w ∣[(2 : ℤ)] g = s • gridCombination N w := by
  rw [gridCombination_slash]
  funext z
  simp only [gridCombination, Function.comp_apply, hw, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

/-- Each integral slash of the weighted sum is bounded at infinity. -/
theorem gridCombination_bounded_slash (N : ℕ) [NeZero N] (w : (Fin 2 → ZMod N) → ℂ)
    (g : SL(2, ℤ)) :
    IsBoundedAtImInfty (gridCombination N w ∣[(2 : ℤ)] g) := by
  rw [gridCombination_slash]
  have hEq : gridCombination N (w ∘ (residueEquiv N g).symm) =
      ∑ a : Fin 2 → ZMod N, (w ((residueEquiv N g).symm a)) • latticeDiff N (residueLift a) 0 := by
    funext z
    simp [gridCombination, Finset.sum_apply]
  rw [hEq]
  let A := boundedAtImInftySubalgebra ℂ
  change (∑ a : Fin 2 → ZMod N,
    (w ((residueEquiv N g).symm a)) • latticeDiff N (residueLift a) 0) ∈ A
  apply A.sum_mem
  intro a _
  apply A.smul_mem
  rw [latticeDiff_eq_gridSeries_sub]
  exact A.sub_mem (gridSeries_bounded N _) (gridSeries_bounded N _)


end ZInQ.Manuscript.RC.EisSlash
