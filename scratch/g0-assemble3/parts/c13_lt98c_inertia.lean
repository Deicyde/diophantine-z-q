-- (g0-assemble3: scratch/linked-tate/parts/98c_inertia.lean, verbatim)
/-! ## linked-tate: `LocalInertiaGlobal` proved (Mathlib)

The place is the comap `v` of the valuation `‖·‖` of `ℚ̄_p` along the embedding `ℚ̄ → ℚ̄_p` that
`decomp` uses (`embP`, with `embP ∘ decomp σ = σ ∘ embP`, Mathlib's `restrictNormal_commutes`):
`decomp σ` preserves `v` (`σ` is an isometry, `PkgI4.norm_gqp_apply`), `p ∈ v.nonunits`
(`‖p‖ = p⁻¹`), and for `σ` in the inertia set `decomp σ` acts trivially on the residue field of
`v` (`‖σx − x‖ < 1` for `‖x‖ ≤ 1`). First compiled standalone over Mathlib
(`scratch/linked-tate/test/LocalInertia.lean`). -/

section LocalInertiaSec

noncomputable section

open scoped Pointwise

namespace UnramTate

variable (p : ℕ) [Fact p.Prime]

/-- The embedding `ℚ̄ → ℚ̄_p` that `decomp` uses. -/
def embP : PkgI4.Qbar →+* PadicAlgCl p :=
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]).toRingHom

theorem embP_decomp (σ : PkgI4.GQp p) (x : PkgI4.Qbar) : embP p (PkgI4.decomp p σ x) = σ (embP p x) := by
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[p]) :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]).toRingHom.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

theorem localInertiaGlobal_at (σ : PkgI4.GQp p) (hσ : σ ∈ (LadicCond.inertiaSet : Set (PkgI4.GQp p))) :
    ∃ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p ∧
      ∃ τ ∈ v.inertiaSubgroup ℚ, ((τ : v.decompositionSubgroup ℚ) : PkgI4.GQ) = PkgI4.decomp p σ := by
  let w : Valuation PkgI4.Qbar NNReal := (Valued.v : Valuation (PadicAlgCl p) NNReal).comap (embP p)
  let v := w.valuationSubring
  have hmem : ∀ x, x ∈ v ↔ ‖embP p x‖ ≤ 1 := by
    intro x
    show Valued.v (embP p x) ≤ 1 ↔ _
    rw [← NNReal.coe_le_coe, PadicAlgCl.valuation_coe, NNReal.coe_one]
  have hnorm : ∀ (g : PkgI4.GQp p) (x : PkgI4.Qbar), ‖embP p (PkgI4.decomp p g x)‖ = ‖embP p x‖ := by
    intro g x; rw [embP_decomp, PkgI4.norm_gqp_apply]
  have hτv : PkgI4.decomp p σ ∈ v.decompositionSubgroup ℚ := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hmem, hmem, ← map_inv]
    exact iff_of_eq (congrArg (· ≤ (1 : ℝ)) (hnorm σ⁻¹ x))
  have hnu : ∀ x : PkgI4.Qbar, ‖embP p x‖ < 1 → x ∈ v.nonunits := by
    intro x hx
    rw [ValuationSubring.mem_nonunits_iff_or]
    by_cases h0 : x = 0
    · exact Or.inl h0
    · right
      rw [hmem, map_inv₀, norm_inv]
      have hpos : 0 < ‖embP p x‖ := norm_pos_iff.mpr ((map_ne_zero _).mpr h0)
      intro h
      have := (inv_le_one₀ hpos).mp h
      linarith
  refine ⟨v, ?_, ⟨⟨PkgI4.decomp p σ, hτv⟩, ?_, rfl⟩⟩
  · apply hnu
    rw [map_natCast]
    have : ‖((p : ℚ_[p]) : PadicAlgCl p)‖ = ‖(p : ℚ_[p])‖ := PadicAlgCl.norm_extends p _
    rw [map_natCast] at this
    rw [this, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  · rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    ext r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    change (⟨PkgI4.decomp p σ, hτv⟩ : v.decompositionSubgroup ℚ) • IsLocalRing.residue v a =
      IsLocalRing.residue v a
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
    apply hnu
    show ‖embP p (PkgI4.decomp p σ (a : PkgI4.Qbar) - a)‖ < 1
    rw [map_sub, embP_decomp]
    exact hσ _ ((hmem a).mp a.2)

/-- **`LocalInertiaGlobal`, proved.** -/
theorem localInertiaGlobal : LocalInertiaGlobal := fun p _ σ hσ => localInertiaGlobal_at p σ hσ

end UnramTate

end

end LocalInertiaSec

