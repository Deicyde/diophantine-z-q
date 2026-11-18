import ActualPrimePowerDivisionV002

/-!
# Actual finite division-field factoring over a number field

The fields and representations are constructed on the original
geometric point groups inside the original algebraic closure. Finiteness
is proved from native multiplication étaleness. The actual finite
restriction retains inertia and strict wild displacement; no factoring
hypothesis or isomorphic representation model is supplied.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry MonObj

namespace ActualNumberFieldDivision
open ActualFiniteLevel ActualDivisionField ActualPrimePowerDivision

 theorem genuine_division_factor
    (K : Type) [Field K] [NumberField K] (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    ∃ L : FiniteGaloisIntermediateField K Ω,
      L.toIntermediateField = divisionField (Ω := Ω) A (ℓ ^ n) ∧
      ∃ ρ : (L ≃ₐ[K] L) →* MulAut (torsionSubgroup A Ω (ℓ ^ n)),
        Continuous (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L) ∧
        Function.Surjective (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L) ∧
        Function.Injective ρ ∧
        ∀ σ : Ω ≃ₐ[K] Ω, ρ (AlgEquiv.restrictNormalHom L σ) = action A (ℓ ^ n) σ := by
  let L := divisionFieldLevel (Ω := Ω) A ℓ n
  refine ⟨L, rfl, rho A ℓ n, restriction_continuous A (ℓ ^ n),
    restriction_surjective A (ℓ ^ n), rho_faithful A ℓ n, ?_⟩
  exact rho_factors_original A ℓ n

 theorem actual_wild_finite_restriction
    (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (hu : IsUnit (ℓ : O)) (n : ℕ) (σ : Ω ≃ₐ[K] Ω) (hI : PkgI2.IsInertia w σ)
    (hW : ∀ a : Ω, a ≠ 0 → w.valuation (σ a - a) < w.valuation a) :
    ∃ L : FiniteGaloisIntermediateField K Ω,
      L.toIntermediateField = divisionField (Ω := Ω) A (ℓ ^ n) ∧
      PkgI2.IsInertia (w.comap L.toIntermediateField.val.toRingHom)
        (AlgEquiv.restrictNormalHom L σ) ∧
      (∀ a : L, a ≠ 0 → (w.comap L.toIntermediateField.val.toRingHom).valuation
        (AlgEquiv.restrictNormalHom L σ a - a) < (w.comap L.toIntermediateField.val.toRingHom).valuation a) ∧
      Nat.Coprime (orderOf (AlgEquiv.restrictNormalHom L σ)) (ℓ ^ n) := by
  let L := divisionFieldLevel (Ω := Ω) A ℓ n
  refine ⟨L, rfl, actual_inertia_restricts A ℓ n w σ hI, actual_wild_restricts A ℓ n w σ hW, ?_⟩
  exact (WildFiniteRestriction.restriction_order_coprime O w hw ℓ Fact.out hu σ hW L).pow_right n

 theorem uniform_torsion_period
    (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (hu : IsUnit (ℓ : O)) (n : ℕ) (σ : Ω ≃ₐ[K] Ω) (hI : PkgI2.IsInertia w σ)
    (hW : ∀ a : Ω, a ≠ 0 → w.valuation (σ a - a) < w.valuation a) :
    ∃ r : ℕ, 0 < r ∧ Nat.Coprime r (ℓ ^ n) ∧
      ∀ x : A.Pt Ω, x ^ (ℓ ^ n) = 1 → (A.galAct σ)^[r] x = x :=
  uniform_original_period O w hw A ℓ hu n σ hW

end ActualNumberFieldDivision
