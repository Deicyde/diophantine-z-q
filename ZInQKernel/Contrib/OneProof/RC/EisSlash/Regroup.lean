import ZInQKernel.Contrib.OneProof.RC.EisSlash.Residues

/-! Reindexing an iterated lattice sum by the two finite residue classes,
without exchanging the order of the two infinite sums. On-the-spot (c)
for tex 9647–9654, 9762–9764 and 9862–9864. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EisSlash

open Matrix ModularForm UpperHalfPlane EisensteinSeries

/-- Integer division with a residue represented by its least nonnegative lift. -/
def intResidueEquiv (N : ℕ) [NeZero N] : ℤ ≃ ZMod N × ℤ where
  toFun n := (n, n / (N : ℤ))
  invFun r := (N : ℤ) * r.2 + r.1.val
  left_inv n := by
    change (N : ℤ) * (n / (N : ℤ)) + ((n : ZMod N).val : ℤ) = n
    rw [ZMod.val_intCast]
    exact Int.mul_ediv_add_emod n N
  right_inv := by
    rintro ⟨r, n⟩
    apply Prod.ext
    · change (((N : ℤ) * n + r.val : ℤ) : ZMod N) = r
      simp
    · change ((N : ℤ) * n + (r.val : ℤ)) / (N : ℤ) = n
      have hN : (0 : ℤ) < N := by exact_mod_cast NeZero.pos N
      rw [add_comm, Int.add_mul_ediv_left _ _ hN.ne',
        Int.ediv_eq_zero_of_lt (Int.natCast_nonneg _) (by exact_mod_cast r.val_lt), zero_add]

private theorem summable_finite_prod {α β : Type*} [Fintype α] {f : α × β → ℂ}
    (h : ∀ a, Summable (fun b => f (a, b))) : Summable f := by
  apply summable_norm_iff.mp
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
  exact ⟨fun a => (h a).norm, (hasSum_fintype _).summable⟩

/-- Regroup one ordinary integer sum by residues. It suffices to know
summability on each member of the finite partition. -/
theorem sum_residue_rows (N : ℕ) [NeZero N] (f : ℤ → ℂ)
    (hs : ∀ a : ZMod N, Summable (fun n : ℤ => f ((N : ℤ) * n + a.val))) :
    Summable f ∧ ∑' n : ℤ, f n = ∑ a : ZMod N, ∑' n : ℤ, f ((N : ℤ) * n + a.val) := by
  let e := (intResidueEquiv N).symm
  have h : Summable (f ∘ e) := summable_finite_prod hs
  refine ⟨e.summable_iff.mp h, ?_⟩
  rw [← e.tsum_eq f]
  change (∑' x, (f ∘ e) x) = _
  rw [h.tsum_prod, tsum_fintype]
  rfl

private theorem residue_vec (N : ℕ) [NeZero N] (r s : ZMod N) (m n : ℤ) :
    rowResidue N ![(N : ℤ) * m + r.val, (N : ℤ) * n + s.val] = ![r,s] := by
  funext i
  fin_cases i <;> simp [rowResidue, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- The inner row of the periodically weighted lattice. -/
def weightedRow (N : ℕ) (w : (Fin 2 → ZMod N) → ℂ) (z : ℍ) (m : ℤ) : ℂ :=
  ∑' n : ℤ, w (rowResidue N ![m, n]) * eisSummand 2 ![m, n] z

private theorem grid_residue_vec (N : ℕ) (r s : ZMod N) (m n : ℤ) :
    grid N (residueLift ![r,s]) ![m,n] =
      ![(N : ℤ) * m + r.val, (N : ℤ) * n + s.val] := by
  funext i
  fin_cases i <;> rfl

set_option maxHeartbeats 2000000 in
private theorem weightedRow_on_residue (N : ℕ) [NeZero N] (w : (Fin 2 → ZMod N) → ℂ)
    (z : ℍ) (r : ZMod N) (m : ℤ) :
    weightedRow N w z ((N : ℤ) * m + r.val) =
      ∑ s : ZMod N, w ![r, s] * gridRow N (residueLift ![r,s]) z m := by
  unfold weightedRow
  have h (s : ZMod N) : Summable (fun n : ℤ =>
      w (rowResidue N ![(N : ℤ) * m + r.val, (N : ℤ) * n + s.val]) *
        eisSummand 2 ![(N : ℤ) * m + r.val, (N : ℤ) * n + s.val] z) := by
    simpa only [residue_vec, grid_residue_vec] using
      (summable_gridRow_inner N (residueLift ![r,s]) z m).mul_left (w ![r,s])
  rw [(sum_residue_rows N _ h).2]
  simp only [residue_vec, gridRow, grid_residue_vec, tsum_mul_left]

/-- The row sums are summable, and their sum is the finite residue-class
expression when the mean weight is zero. -/
theorem gridCombination_eq_weightedRows (N : ℕ) [NeZero N] (w : (Fin 2 → ZMod N) → ℂ)
    (z : ℍ) (hw : ∑ a, w a = 0) :
    Summable (weightedRow N w z) ∧ gridCombination N w z = ∑' m : ℤ, weightedRow N w z m := by
  classical
  have hs (r : ZMod N) : Summable fun m : ℤ => weightedRow N w z ((N : ℤ) * m + r.val) := by
    simp_rw [weightedRow_on_residue]
    exact summable_sum (s := Finset.univ) fun s _ => (summable_gridRows N (residueLift ![r,s]) z).mul_left _
  refine ⟨(sum_residue_rows N _ hs).1, ?_⟩
  rw [(sum_residue_rows N _ hs).2, gridCombination_eq_rows N w hw]
  simp_rw [weightedRow_on_residue,
    Summable.tsum_finsetSum (fun s (_ : s ∈ Finset.univ) =>
      (summable_gridRows N (residueLift ![_,s]) z).mul_left _), tsum_mul_left]
  let f (a : Fin 2 → ZMod N) := w a * gridSeries N (residueLift a) z
  calc
    _ = ∑ a : ZMod N × ZMod N, f ((finTwoArrowEquiv (ZMod N)).symm a) :=
      ((finTwoArrowEquiv (ZMod N)).symm.sum_comp f).symm
    _ = ∑ r : ZMod N, ∑ s : ZMod N, f ((finTwoArrowEquiv (ZMod N)).symm (r, s)) :=
      Fintype.sum_prod_type _
    _ = _ := rfl


end ZInQ.Manuscript.RC.EisSlash
