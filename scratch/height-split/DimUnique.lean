import ZInQKernel.HDecomp.Faltings.Height

/-! Development file for `MetrizedDimUnique` (merged into `HeightSplit.lean` once it compiles). -/

namespace ZInQ.HeightSplit

open Module NumberField ZInQ.DefFaltings
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **2-torsion of a uniformized group.** If `Φ : ℂ^g → P` is a surjective homomorphism onto a group
with kernel a full lattice `Λ`, then `P` has exactly `2^{2g}` elements with `p² = 1`. -/
theorem card_sq_eq_one_of_uniformization {g : ℕ} {P : Type*} [Group P]
    (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (Φ : (Fin g → ℂ) → P) (hadd : ∀ z w, Φ (z + w) = Φ z * Φ w)
    (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ) (hsurj : Function.Surjective Φ) :
    Nat.card {p : P // p * p = 1} = 2 ^ (2 * g) := by
  classical
  have hhalf : ∀ z : Fin g → ℂ, (2 : ℂ)⁻¹ • z + (2 : ℂ)⁻¹ • z = z := by
    intro z; rw [← add_smul]; norm_num
  have hhalf' : ∀ z : Fin g → ℂ, (2 : ℂ)⁻¹ • (z + z) = z := by
    intro z; rw [← two_smul ℂ z, smul_smul]; norm_num
  let F : Λ → {p : P // p * p = 1} := fun a => ⟨Φ ((2 : ℂ)⁻¹ • (a : Fin g → ℂ)), by
    rw [← hadd, hhalf]; exact (hker _).mpr a.2⟩
  have hF : Function.Surjective F := by
    rintro ⟨p, hp⟩
    obtain ⟨z, rfl⟩ := hsurj p
    have hz : z + z ∈ Λ := (hker _).mp (by rw [hadd]; exact hp)
    exact ⟨⟨z + z, hz⟩, Subtype.ext (by simp only [F]; rw [hhalf'])⟩
  let H : AddSubgroup Λ := (nsmulAddMonoidHom (α := Λ) 2).range
  have hrel : ∀ a b : Λ, F a = F b ↔ -a + b ∈ H := by
    intro a b
    have hsplit : (2 : ℂ)⁻¹ • (b : Fin g → ℂ) =
        (2 : ℂ)⁻¹ • (a : Fin g → ℂ) + (2 : ℂ)⁻¹ • ((-a + b : Λ) : Fin g → ℂ) := by
      simp only [Submodule.coe_add, Submodule.coe_neg, smul_add, smul_neg]; abel
    have h1 : F a = F b ↔ Φ ((2 : ℂ)⁻¹ • ((-a + b : Λ) : Fin g → ℂ)) = 1 := by
      rw [Subtype.ext_iff]
      simp only [F]
      rw [hsplit, hadd]
      constructor
      · intro h
        have := congrArg (fun q => (Φ ((2 : ℂ)⁻¹ • (a : Fin g → ℂ)))⁻¹ * q) h
        simpa using this.symm
      · intro h; rw [h, _root_.mul_one]
    rw [h1, hker]
    constructor
    · intro h
      refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
      simp only [nsmulAddMonoidHom_apply, Submodule.coe_smul_of_tower]
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]; norm_num
    · rintro ⟨c, hc⟩
      have hc' : ((-a + b : Λ) : Fin g → ℂ) = (2 : ℂ) • (c : Fin g → ℂ) := by
        rw [← hc]
        simp only [nsmulAddMonoidHom_apply, Submodule.coe_smul_of_tower]
        rw [← Nat.cast_smul_eq_nsmul ℂ]; norm_num
      rw [hc', smul_smul]; norm_num
  have e : {p : P // p * p = 1} ≃ Λ ⧸ H :=
    (Setoid.quotientKerEquivOfSurjective F hF).symm.trans
      (Quotient.congrRight fun a b => by
        rw [QuotientAddGroup.leftRel_apply]; exact hrel a b)
  have := ZLattice.module_free ℝ Λ
  have := ZLattice.module_finite ℝ Λ
  rw [Nat.card_congr e, ← AddSubgroup.index, AddSubgroup.index_range_nsmul, ZLattice.rank ℝ Λ]
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

/-- **`MetrizedDimUnique` (the glue statement of `HeightSplit.lean`, proved).** -/
theorem metrizedDimUnique_aux {K : Type} [Field K] (A : PkgI3.AbVar K) (L : Type) [Field L]
    [NumberField L] [Algebra K L] (g g' : ℕ) (M : MetrizedModel A L g)
    (M' : MetrizedModel A L g') (hMM : M.model = M'.model) : g = g' := by
  obtain ⟨𝒢, D, hl, ha⟩ := M
  obtain ⟨𝒢', D', hl', ha'⟩ := M'
  dsimp only at hMM
  subst hMM
  obtain ⟨τ⟩ : Nonempty (L →+* ℂ) := ⟨(IsAlgClosed.lift : L →ₐ[ℚ] ℂ).toRingHom⟩
  obtain ⟨Φ, hΦ, -⟩ := ha τ
  obtain ⟨Φ', hΦ', -⟩ := ha' τ
  have := D.periods_discrete τ
  have := D.periods_isZLattice τ
  have := D'.periods_discrete τ
  have := D'.periods_isZLattice τ
  have h1 := card_sq_eq_one_of_uniformization (D.periods τ) Φ hΦ.1 hΦ.2.1 hΦ.2.2.1
  have h2 := card_sq_eq_one_of_uniformization (D'.periods τ) Φ' hΦ'.1 hΦ'.2.1 hΦ'.2.2.1
  rw [h1] at h2
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

end ZInQ.HeightSplit

#print axioms ZInQ.HeightSplit.metrizedDimUnique_aux
