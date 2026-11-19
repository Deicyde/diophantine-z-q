import OriginalTateLatticeContinuity
import ActualWildProPrimeKrull

/-! # Original-object hypothesis contracts for wild image finiteness -/

noncomputable section
set_option autoImplicit false

namespace OriginalWildImageContracts

open CategoryTheory AlgebraicGeometry MonObj
open OriginalWildTateImage NativeTateCongruence

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

theorem integral_original [NumberField K] [IsAlgClosure K Ω]
    (O : ValuationSubring K) [IsDiscreteValuationRing O] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K)
    (ell : ℕ) [Fact ell.Prime] (hu : IsUnit (ell : O)) :
    (Set.range fun sigma : WildFiniteGroup.strictDisplacementGroup (K := K) w =>
      originalTateRep A ell sigma.1).Finite :=
  original_integral_wild_image_finite O w hw A ell hu

theorem rational_original [NumberField K]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O) (A : PkgI3.AbVar K)
    (ell : ℕ) [Fact ell.Prime] (hu : IsUnit (ell : O)) :
    (Set.range fun sigma : WildFiniteGroup.strictDisplacementGroup (K := K) w =>
      A.galRep ell sigma.1).Finite :=
  original_rational_wild_image_finite O w hw A ell hu

theorem integral_inertia_wild [NumberField K] [IsAlgClosure K Ω]
    (O : ValuationSubring K) [IsDiscreteValuationRing O] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K)
    (ell : ℕ) [Fact ell.Prime] (hu : IsUnit (ell : O)) :
    (Set.range fun sigma : {sigma : Ω ≃ₐ[K] Ω // PkgI2.IsInertia w sigma ∧
        ∀ x : Ω, x ≠ 0 → w.valuation (sigma x - x) < w.valuation x} =>
      originalTateRep A ell sigma.1).Finite := by
  apply (original_integral_wild_image_finite O w hw A ell hu).subset
  rintro f ⟨sigma, rfl⟩
  exact ⟨⟨sigma.1, sigma.2.2⟩, rfl⟩

theorem rational_inertia_wild [NumberField K]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K))
    (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O) (A : PkgI3.AbVar K)
    (ell : ℕ) [Fact ell.Prime] (hu : IsUnit (ell : O)) :
    (Set.range fun sigma : {sigma : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K //
        PkgI2.IsInertia w sigma ∧ ∀ x : AlgebraicClosure K, x ≠ 0 →
          w.valuation (sigma x - x) < w.valuation x} => A.galRep ell sigma.1).Finite := by
  apply (original_rational_wild_image_finite O w hw A ell hu).subset
  rintro f ⟨sigma, rfl⟩
  exact ⟨⟨sigma.1, sigma.2.2⟩, rfl⟩

theorem lattice_original [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (ell : ℕ) [Fact ell.Prime] :
    Module.Free ℤ_[ell] (PkgI3.Tate.T ell (Additive (A.Pt Ω))) ∧
    Module.Finite ℤ_[ell] (PkgI3.Tate.T ell (Additive (A.Pt Ω))) :=
  original_tate_finite_free A ell

theorem basis_original [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (ell : ℕ) [Fact ell.Prime] :
    ∃ r : ℕ, Nonempty (PkgI3.Tate.T ell (Additive (A.Pt Ω)) ≃ₗ[ℤ_[ell]] (Fin r → ℤ_[ell])) :=
  original_tate_basis A ell

theorem continuous_original [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (ell : ℕ) [Fact ell.Prime] :
    ∃ r : ℕ, ∃ b : Module.Basis (Fin r) ℤ_[ell] (PkgI3.Tate.T ell (Additive (A.Pt Ω))),
      Continuous (originalTateMatrix A ell b) :=
  original_continuous_tate_basis A ell

theorem residue_prime_original [NumberField K] [IsAlgClosure K Ω]
    (O : ValuationSubring K) [IsDiscreteValuationRing O] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (ell : ℕ) [Fact ell.Prime] (hu : IsUnit (ell : O)) :
    ∃ p : ℕ, p.Prime ∧ CharP (IsLocalRing.ResidueField w) p ∧ p ≠ ell := by
  obtain ⟨p, hp, hchar⟩ := ValuationResidueCharacteristic.numberField_residue_prime O
  haveI : CharP (IsLocalRing.ResidueField O) p := hchar
  haveI : CharP (IsLocalRing.ResidueField (w.comap (algebraMap K Ω))) p := by rw [hw]; infer_instance
  haveI : CharP (IsLocalRing.ResidueField w) p :=
    (ValuationResidueCharacteristic.residue_charP_iff w (algebraMap K Ω) p).mp inferInstance
  exact ⟨p, hp, inferInstance, ValuationResidueCharacteristic.prime_ne_of_isUnit O p ell hu⟩

#check integral_original
#print axioms integral_original
#check rational_original
#print axioms rational_original
#check integral_inertia_wild
#print axioms integral_inertia_wild
#check rational_inertia_wild
#print axioms rational_inertia_wild
#check lattice_original
#print axioms lattice_original
#check basis_original
#print axioms basis_original
#check continuous_original
#print axioms continuous_original
#check residue_prime_original
#print axioms residue_prime_original

end OriginalWildImageContracts
