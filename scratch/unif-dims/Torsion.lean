import Mathlib

/-! # unif-dims: the 2-torsion of `ℂ^g/Λ` has `4^g` elements (Mathlib only)

If `Φ : ℂ^g → G` is a surjective homomorphism onto a group with kernel a discrete full `ℤ`-lattice
`Λ`, then `#{p ∈ G | p² = 1} = 2^(2g)`. Hence the dimension `g` of such a "uniformization" is
determined by the abstract group `G`. -/

namespace ZInQ.UnifDims

open Module

variable {G : Type*} [Group G] {g : ℕ}

/-- The additive homomorphism `λ ↦ Φ(λ/2)` from the lattice to `G`. -/
noncomputable def halfHom (Φ : (Fin g → ℂ) → G) (Λ : Submodule ℤ (Fin g → ℂ))
    (hmul : ∀ z w, Φ (z + w) = Φ z * Φ w) : Λ →+ Additive G :=
  AddMonoidHom.mk' (fun l => Additive.ofMul (Φ ((1 / 2 : ℂ) • (l : Fin g → ℂ)))) (by
    intro a b
    simp only [Submodule.coe_add, smul_add, hmul]
    rfl)

/-- **The 2-torsion of a uniformized group.** -/
theorem card_twoTorsion (Φ : (Fin g → ℂ) → G) (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (hmul : ∀ z w, Φ (z + w) = Φ z * Φ w) (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ)
    (hsurj : Function.Surjective Φ) : Nat.card {p : G // p * p = 1} = 2 ^ (2 * g) := by
  set ψ := halfHom Φ Λ hmul
  -- rank of `Λ`
  have hrank : finrank ℤ Λ = 2 * g := by
    rw [ZLattice.rank ℝ Λ, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  let b := Module.finBasisOfFinrankEq ℤ Λ hrank
  -- `Λ ⧸ ker ψ ≃ range ψ ≃ G[2]`
  have hrange : ∀ p : G, p * p = 1 ↔ Additive.ofMul p ∈ ψ.range := by
    intro p
    constructor
    · intro hp
      obtain ⟨z, rfl⟩ := hsurj p
      have h2 : (2 : ℂ) • z ∈ Λ := by
        rw [← hker, two_smul, hmul, hp]
      refine ⟨⟨_, h2⟩, ?_⟩
      show Additive.ofMul (Φ ((1 / 2 : ℂ) • (2 : ℂ) • z)) = _
      rw [smul_smul]
      norm_num
    · rintro ⟨l, hl⟩
      have hl' : Φ ((1 / 2 : ℂ) • (l : Fin g → ℂ)) = p := hl
      rw [← hl', ← hmul, ← add_smul]
      norm_num
      exact (hker _).mpr l.2
  have hker' : ψ.ker = (AddSubgroup.pi Set.univ (fun _ : Fin (2 * g) =>
      AddSubgroup.zmultiples (2 : ℤ))).comap b.equivFun.toLinearMap.toAddMonoidHom := by
    ext l
    simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_comap, AddSubgroup.mem_pi, Set.mem_univ,
      true_implies, Int.mem_zmultiples_iff]
    show Φ ((1 / 2 : ℂ) • (l : Fin g → ℂ)) = 1 ↔ _
    rw [hker]
    constructor
    · intro h i
      set μ : Λ := ⟨_, h⟩
      have hl : l = (2 : ℤ) • μ := by
        ext1
        simp only [SetLike.val_smul, μ]
        rw [← Int.cast_smul_eq_zsmul ℂ, smul_smul]
        norm_num
      refine ⟨b.equivFun μ i, ?_⟩
      have := congrArg (fun x => b.equivFun x i) hl
      simp only [LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul] at this
      exact this
    · intro h
      choose d hd using h
      let μ : Λ := b.equivFun.symm d
      have hl : l = (2 : ℤ) • μ := by
        apply b.equivFun.injective
        ext i
        simp only [LinearEquiv.map_smul, Pi.smul_apply, smul_eq_mul, μ,
          LinearEquiv.apply_symm_apply]
        exact hd i
      have : (1 / 2 : ℂ) • (l : Fin g → ℂ) = (μ : Fin g → ℂ) := by
        rw [hl, SetLike.val_smul, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
        norm_num
      rw [this]
      exact μ.2
  have hidx : ψ.ker.index = 2 ^ (2 * g) := by
    rw [hker', AddSubgroup.index_comap_of_surjective _ b.equivFun.surjective,
      AddSubgroup.index_pi]
    simp [Int.index_zmultiples]
  calc Nat.card {p : G // p * p = 1}
      = Nat.card ψ.range := Nat.card_congr
        (Equiv.subtypeEquiv Additive.ofMul (fun p => hrange p))
    _ = Nat.card (Λ ⧸ ψ.ker) := Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv.symm
    _ = 2 ^ (2 * g) := hidx

/-- **The dimension of a uniformization is determined by the group.** -/
theorem dim_eq_of_unif {g g' : ℕ} (Φ : (Fin g → ℂ) → G) (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ' : (Fin g' → ℂ) → G) (Λ' : Submodule ℤ (Fin g' → ℂ))
    (hd : DiscreteTopology Λ) (hz : IsZLattice ℝ Λ) (hd' : DiscreteTopology Λ')
    (hz' : IsZLattice ℝ Λ')
    (hmul : ∀ z w, Φ (z + w) = Φ z * Φ w) (hker : ∀ z, Φ z = 1 ↔ z ∈ Λ)
    (hsurj : Function.Surjective Φ)
    (hmul' : ∀ z w, Φ' (z + w) = Φ' z * Φ' w) (hker' : ∀ z, Φ' z = 1 ↔ z ∈ Λ')
    (hsurj' : Function.Surjective Φ') : g = g' := by
  have h1 := card_twoTorsion Φ Λ hmul hker hsurj
  have h2 := card_twoTorsion Φ' Λ' hmul' hker' hsurj'
  rw [h1] at h2
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

end ZInQ.UnifDims

#print axioms ZInQ.UnifDims.dim_eq_of_unif
