import ZInQKernel.Contrib.LocalSquareRoot.Tower

/-!
# Complex-valued finite square roots and actual inflation

The finite arithmetic is the frozen `sqrt_criterion_level_pow` proof in `FiniteLevel`.
Its character target is `Additive ℂˣ`, justified by the proved Baer/divisibility bridge.
This module only changes multiplicative notation, supplies the true enlarged-level
side conditions, and inflates through actual normal restriction.
-/

namespace ZInQ.Contrib.LocalSquareRoot

open GlueSqrtDisj

section Tau

variable (p : ℕ) [hp : Fact p.Prime]

/-- The finite automorphism with cyclotomic coordinates `(-1,1)` is an involution. -/
theorem tau_square_eq_one (K : Type) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
    [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    (k m : ℕ) [NeZero m] (hcop : p.Coprime m)
    [IsCyclotomicExtension {p ^ k * m} ℚ_[p] K]
    (τ : Gal(K/ℚ_[p])) (hτ : galToProd (p := p) (L := K) k m τ = (-1, 1)) :
    τ ^ 2 = 1 := by
  apply galToProd_injective (p := p) (L := K) k m hcop
  rw [map_pow, hτ, map_one]
  ext <;> simp

/-- The actual restriction maps carry `tau_-1` to `tau_-1` at the lower level. -/
theorem tau_restrict_acts (K L : Type) [Field K] [Field L]
    [Algebra ℚ_[p] K] [Algebra ℤ_[p] K] [IsScalarTower ℤ_[p] ℚ_[p] K]
    [FiniteDimensional ℚ_[p] K] [IsGalois ℚ_[p] K]
    [Algebra ℚ_[p] L] [Algebra ℤ_[p] L] [IsScalarTower ℤ_[p] ℚ_[p] L]
    [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]
    (k m k' m' : ℕ) [NeZero m] [NeZero m']
    [IsCyclotomicExtension {p ^ k * m} ℚ_[p] K]
    [IsCyclotomicExtension {p ^ k' * m'} ℚ_[p] L]
    [Algebra K L] [IsScalarTower ℚ_[p] K L] (hk : k ≤ k') (hm : m ∣ m')
    (τ : Gal(L/ℚ_[p])) (hτ : galToProd (p := p) (L := L) k' m' τ = (-1, 1)) :
    galToProd (p := p) (L := K) k m (τ.restrictNormal K) = (-1, 1) := by
  obtain ⟨h1, h2⟩ := galToProd_restrict (p := p) (L := L) k' m' K k m hk hm τ
  rw [hτ] at h1 h2
  apply Prod.ext
  · apply Units.ext
    rw [h1]
    simp [-ZMod.castHom_apply]
  · apply Units.ext
    rw [h2]
    simp [-ZMod.castHom_apply]

end Tau

/-- Finite-level sufficiency, inflated to the actual absolute Galois group.
There is no local-Kronecker-Weber assumption in this direction. -/
theorem exists_inflated_squareRoot (p : ℕ) [hp : Fact p.Prime]
    (k m : ℕ) [NeZero m] (hcop : p.Coprime m)
    (τ : Gal(muField p (p ^ k * m)/ℚ_[p]))
    (hτ : galToProd (p := p) (L := muField p (p ^ k * m)) k m τ = (-1, 1))
    (χ : Gal(muField p (p ^ k * m)/ℚ_[p]) →* ℂˣ) (hχ : χ τ = 1) :
    ∃ φ : Field.absoluteGaloisGroup ℚ_[p] →* ℂˣ,
      IsLocallyConstant φ ∧ ∀ g, φ g ^ 2 = χ (g.restrictNormal (muField p (p ^ k * m))) := by
  let f := orderOf (ZMod.unitOfCoprime p hcop)
  let m' := p ^ (2 * f) - 1
  haveI : NeZero m' := ⟨(enlarged_level_pos p m hcop).ne'⟩
  let K := muField p (p ^ k * m)
  let L := muField p (p ^ (k + 1) * m')
  have hKL : K ≤ L := muField_le_level p k m hcop
  letI : Algebra K L := fieldInclusionAlgebra K L hKL
  letI : IsScalarTower ℚ_[p] K L := fieldInclusion_scalarTower_base K L hKL
  letI : IsScalarTower K L (PadicAlgCl p) := fieldInclusion_scalarTower_top K L hKL
  have hχa : χ.toAdditive (Additive.ofMul τ) = 0 := congrArg Additive.ofMul hχ
  obtain ⟨ψ, hψ⟩ := (sqrt_criterion_level_pow (p := p) (L := L) K k m hcop τ hτ
    χ.toAdditive).mpr hχa
  let ψm : Gal(L/ℚ_[p]) →* ℂˣ := MonoidHom.toAdditive.symm ψ
  refine ⟨ψm.comp (AlgEquiv.restrictNormalHom L),
    inflatedCharacter_isLocallyConstant ℚ_[p] L ψm, ?_⟩
  intro g
  change ψm (g.restrictNormal L) ^ 2 = χ (g.restrictNormal K)
  rw [← restrictNormal_trans (K := K) (L := L) g]
  exact congrArg Additive.toMul (hψ (g.restrictNormal L))

end ZInQ.Contrib.LocalSquareRoot
