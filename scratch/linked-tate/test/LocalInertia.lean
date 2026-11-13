import Mathlib
open scoped Pointwise

noncomputable section
namespace LITest

abbrev Qbar := AlgebraicClosure ℚ
abbrev GQ := Qbar ≃ₐ[ℚ] Qbar
variable (p : ℕ) [Fact p.Prime]
abbrev GQp := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p
def decomp : GQp p →* GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p]) :
    Field.absoluteGaloisGroup ℚ_[p] →* Field.absoluteGaloisGroup ℚ)
def LiesOver (v : ValuationSubring Qbar) (p : ℕ) : Prop := (p : Qbar) ∈ v.nonunits
def inertiaSet : Set (GQp p) := {σ | ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1}
theorem norm_gqp_apply (σ : GQp p) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv σ x).symm

/-- The embedding `ℚ̄ → ℚ̄_p` that `decomp` uses. -/
def embP : Qbar →+* PadicAlgCl p :=
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]).toRingHom

theorem embP_decomp (σ : GQp p) (x : Qbar) : embP p (decomp p σ x) = σ (embP p x) := by
  letI : Algebra ℚ ℚ_[p] := (algebraMap ℚ ℚ_[p]).toAlgebra
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure ℚ_[p]) :=
    (IsAlgClosed.lift : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ_[p]).toRingHom.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars ℚ) (AlgebraicClosure ℚ) x

theorem localInertiaGlobal (σ : GQp p) (hσ : σ ∈ inertiaSet p) :
    ∃ v : ValuationSubring Qbar, LiesOver v p ∧
      ∃ τ ∈ v.inertiaSubgroup ℚ, ((τ : v.decompositionSubgroup ℚ) : GQ) = decomp p σ := by
  let w : Valuation Qbar NNReal := (Valued.v : Valuation (PadicAlgCl p) NNReal).comap (embP p)
  let v := w.valuationSubring
  have hmem : ∀ x, x ∈ v ↔ ‖embP p x‖ ≤ 1 := by
    intro x
    show Valued.v (embP p x) ≤ 1 ↔ _
    rw [← NNReal.coe_le_coe, PadicAlgCl.valuation_coe, NNReal.coe_one]
  have hnorm : ∀ (g : GQp p) (x : Qbar), ‖embP p (decomp p g x)‖ = ‖embP p x‖ := by
    intro g x; rw [embP_decomp, norm_gqp_apply]
  have hτv : decomp p σ ∈ v.decompositionSubgroup ℚ := by
    rw [MulAction.mem_stabilizer_iff]
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, hmem, hmem, ← map_inv]
    exact iff_of_eq (congrArg (· ≤ (1 : ℝ)) (hnorm σ⁻¹ x))
  have hnu : ∀ x : Qbar, ‖embP p x‖ < 1 → x ∈ v.nonunits := by
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
  refine ⟨v, ?_, ⟨⟨decomp p σ, hτv⟩, ?_, rfl⟩⟩
  · apply hnu
    rw [map_natCast]
    have : ‖((p : ℚ_[p]) : PadicAlgCl p)‖ = ‖(p : ℚ_[p])‖ := PadicAlgCl.norm_extends p _
    rw [map_natCast] at this
    rw [this, Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  · rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    ext r
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    change (⟨decomp p σ, hτv⟩ : v.decompositionSubgroup ℚ) • IsLocalRing.residue v a =
      IsLocalRing.residue v a
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
    apply hnu
    show ‖embP p (decomp p σ (a : Qbar) - a)‖ < 1
    rw [map_sub, embP_decomp]
    exact hσ _ ((hmem a).mp a.2)

end LITest
