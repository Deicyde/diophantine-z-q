/-! ## linked-tate: `UpperAbsInertia` proved (Mathlib)

For `t > 0`, the lower index `sInf {u ≥ −1 | t ≤ φ_L(u)}` is `≥ 0` (`φ_L ≤ 0` on `u ≤ 0`, an
integral of a nonnegative function), so `G^t(L) ⊆ G_0(L)`: `‖σx − x‖ ≤ ‖ϖ‖^{n+1} < 1` on the unit
ball of `L`. Every `x ∈ ℚ̄_p` lies in the finite Galois normal closure of `ℚ_p(x)`. First compiled
standalone over Mathlib (`scratch/linked-tate/test/UpperAbs.lean`). -/

section UpperAbsSec

noncomputable section

namespace UnramTate

variable {p : ℕ} [Fact p.Prime]

theorem phiAt_nonpos (L : LadicCond.Fld p) {u : ℝ} (hu : u ≤ 0) : LadicCond.phiAt L u ≤ 0 := by
  unfold LadicCond.phiAt
  rw [intervalIntegral.integral_symm]
  have : 0 ≤ ∫ t in u..(0 : ℝ), (LadicCond.ramCardR L t : ℝ) / (LadicCond.ramCard L 0 : ℝ) :=
    intervalIntegral.integral_nonneg hu (fun _ _ => by positivity)
  linarith

theorem sInf_nonneg_of_pos (L : LadicCond.Fld p) {t : ℝ} (ht : 0 < t) :
    0 ≤ sInf {u : ℝ | -1 ≤ u ∧ t ≤ LadicCond.phiAt L u} := by
  rcases Set.eq_empty_or_nonempty {u : ℝ | -1 ≤ u ∧ t ≤ LadicCond.phiAt L u} with h | h
  · rw [h, Real.sInf_empty]
  · apply le_csInf h
    rintro u ⟨-, hu⟩
    by_contra hneg
    push Not at hneg
    have := phiAt_nonpos L hneg.le
    linarith

theorem upperSet_sub (L : LadicCond.Fld p) {t : ℝ} (ht : 0 < t) (σ : PkgI4.GQp p) (hσ : σ ∈ LadicCond.upperSet L t) :
    ∀ x ∈ L, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1 := by
  have h0 := sInf_nonneg_of_pos L ht
  unfold LadicCond.upperSet LadicCond.ramSetR at hσ
  rw [if_neg (show ¬ _ ≤ (-1 : ℝ) by linarith)] at hσ
  obtain ⟨ϖ, hϖ, hle⟩ := hσ
  intro x hx hx1
  refine lt_of_le_of_lt (hle x hx hx1) ?_
  exact pow_lt_one₀ (norm_nonneg _) hϖ.2.1 (Nat.succ_ne_zero _)

theorem upperAbs_subset_inertiaSet' (t : ℝ) (ht : 0 < t) :
    LadicCond.upperAbs p t ⊆ (LadicCond.inertiaSet : Set (PkgI4.GQp p)) := by
  intro σ hσ x hx
  let K : LadicCond.Fld p := IntermediateField.adjoin ℚ_[p] {x}
  haveI hKfin : FiniteDimensional ℚ_[p] K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  let L : LadicCond.Fld p := IntermediateField.normalClosure ℚ_[p] K (LadicCond.Kbar p)
  have hL : LadicCond.IsFinGal L := ⟨inferInstance, inferInstance⟩
  have hxL : x ∈ L := IntermediateField.le_normalClosure K (IntermediateField.mem_adjoin_simple_self ℚ_[p] x)
  exact upperSet_sub L ht σ (hσ L hL) x hxL hx

/-- **`UpperAbsInertia`, proved.** -/
theorem upperAbsInertia : UpperAbsInertia := fun _ _ t ht => upperAbs_subset_inertiaSet' t ht

end UnramTate

end

end UpperAbsSec

#print axioms UnramTate.upperAbsInertia
