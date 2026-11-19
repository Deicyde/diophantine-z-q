import ZInQKernel.Contrib.CloudR2CM.SerreTate.FiniteInertiaStatements
import ZInQKernel.Contrib.CloudR2CM.SerreTate.P1.WildImageComparison
import ZInQKernel.Contrib.CloudR2CM.SerreTate.P1.CMGaloisProof
import OriginalWildImageContracts
import FrobLift.WildSubgroupV001
import FrobLift.WildInertiaV001

/-!
# Conditional finite inertia from the actual CM and wild-image proofs

The actual tame-generator and commuting-image consumers are explicit,
named premises. The original CM commutation, Frobenius lift, continuous
original matrix action and finite wild image are supplied by their actual
proofs. No open arithmetic input is silently promoted to a theorem.
-/

set_option autoImplicit false

noncomputable section

open scoped CategoryTheory.MonObj TensorProduct

open Topology Matrix

namespace HDec.CMSerreTate.P1

/-- The literal actual tame-density condition used by the commuting
finite-image consumer, with the original inertia and wild subgroup. -/
def ActualTameDensity {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (w : ValuationSubring Ω) (τ : Ω ≃ₐ[K] Ω) : Prop :=
  {σ : Ω ≃ₐ[K] Ω | _root_.PkgI2.IsInertia w σ} ⊆
    closure {σ : Ω ≃ₐ[K] Ω | ∃ n : ℤ, ∃ π ∈ _root_.FrobLift.wildSubgroup w, σ = τ ^ n * π}

/-- OPEN arithmetic input: the actual tame generator, not merely a
generic compact-group procyclicity template. -/
def ActualTameGeneratorInput : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring (AlgebraicClosure K)),
    w.comap (algebraMap K (AlgebraicClosure K)) = O →
    ∃ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      _root_.PkgI2.IsInertia w τ ∧ ActualTameDensity w τ

/-- OPEN consumer input at its literal group-valued type. It requires
finite original wild image, actual tame density and Frobenius commutation;
it does not assume the desired CM finite-inertia conclusion. -/
def CommutingFiniteInput : Prop :=
  ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (G : Type) [Group G] [TopologicalSpace G] [T1Space G]
    (w : ValuationSubring Ω) (ρ : (Ω ≃ₐ[K] Ω) →* G),
    Continuous ρ →
    ∀ [Finite ((_root_.FrobLift.wildSubgroup w).map ρ)]
      (φ : Ω ≃ₐ[K] Ω), φ ∈ w.decompositionSubgroup K →
      ∀ (q : ℕ), (∀ x : Ω, x ∈ w → w.valuation (φ x - x ^ q) < 1) →
      ∀ (τ : Ω ≃ₐ[K] Ω), _root_.PkgI2.IsInertia w τ → 2 ≤ q →
        Commute (ρ φ) (ρ τ) → ActualTameDensity w τ →
        (ρ '' {σ : Ω ≃ₐ[K] Ω | _root_.PkgI2.IsInertia w σ}).Finite

/-- CONDITIONAL P1: only the explicitly named actual-tame and
commuting-finite consumers remain premises. The actual CM and transfer
nodes, the Frobenius lift and finite wild-image proof are not assumptions. -/
theorem p1FiniteInertia_conditional (hTame : ActualTameGeneratorInput)
    (hCommuting : CommutingFiniteInput) : HDec.CMSerreTate.P1FiniteInertia := by
  intro K hK hNF A hA k hk hNFk R hR hCM O hO hResid w hw ℓ hPrime hUnit
  have hGal : HDec.CMSerreTate.GaloisImageAbelian A ℓ :=
    cmGaloisImageAbelian_proved K A hA k R hR hCM ℓ
  obtain ⟨r, b, hContinuous⟩ := _root_.OriginalWildTateImage.original_continuous_tate_basis
    (Ω := AlgebraicClosure K) A ℓ
  let G := Matrix.GeneralLinearGroup (Fin r) ℤ_[ℓ]
  let ρ : (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →* G :=
    _root_.NativeTateCongruence.originalTateMatrix A ℓ b
  have hEnd := _root_.OriginalWildTateImage.original_integral_wild_image_finite O w hw A ℓ hUnit
  have hVal : (Set.range fun σ : _root_.WildFiniteGroup.strictDisplacementGroup (K := K) w =>
      (ρ σ.1).val).Finite := by
    let f : Module.End ℤ_[ℓ] (A.T ℓ) → Matrix (Fin r) (Fin r) ℤ_[ℓ] :=
      LinearMap.toMatrixAlgEquiv b
    have he : (fun σ : _root_.WildFiniteGroup.strictDisplacementGroup (K := K) w => (ρ σ.1).val) =
        f ∘ (fun σ : _root_.WildFiniteGroup.strictDisplacementGroup (K := K) w =>
          _root_.NativeTateCongruence.originalTateRep A ℓ σ.1) := by
      funext σ
      apply Matrix.ext
      intro i j
      simpa only [ρ, f, Function.comp_apply, LinearMap.toMatrixAlgEquiv_apply,
        LinearMap.toMatrix_apply] using
        (_root_.NativeTateCongruence.original_matrix_entry A ℓ b σ.1 i j)
    rw [he, Set.range_comp]
    exact hEnd.image f
  have hRange : (Set.range fun σ : _root_.WildFiniteGroup.strictDisplacementGroup (K := K) w =>
      ρ σ.1).Finite := by
    have hImage : ((fun g : G => g.val) ''
        (Set.range fun σ : _root_.WildFiniteGroup.strictDisplacementGroup (K := K) w => ρ σ.1)).Finite := by
      rw [← Set.range_comp]
      exact hVal
    exact Set.Finite.of_finite_image hImage Units.val_injective.injOn
  have hWSet : ((_root_.FrobLift.wildSubgroup w).map ρ : Set G).Finite := by
    apply hRange.subset
    rintro g ⟨σ, hσ, hEq⟩
    exact ⟨⟨σ, hσ⟩, hEq⟩
  letI : Finite ((_root_.FrobLift.wildSubgroup w).map ρ) := hWSet.to_subtype
  obtain ⟨τ, hτ, hDensity⟩ := hTame K O w hw
  obtain ⟨φ, hφ, hq, hCong, _⟩ := _root_.FrobLift.frobenius_lift_wild_inertia hw
  have hEndCommute : Commute (_root_.NativeTateCongruence.originalTateRep A ℓ φ)
      (_root_.NativeTateCongruence.originalTateRep A ℓ τ) := by
    change Commute (_root_.ReductSplit.galTΩ A ℓ φ) (_root_.ReductSplit.galTΩ A ℓ τ)
    exact hGal φ τ
  have hAction : _root_.NativeTateCongruence.originalTateRep A ℓ (φ * τ) =
      _root_.NativeTateCongruence.originalTateRep A ℓ (τ * φ) := by
    rw [map_mul, map_mul]
    exact hEndCommute.eq
  have hCommute : Commute (ρ φ) (ρ τ) := by
    change ρ φ * ρ τ = ρ τ * ρ φ
    rw [← ρ.map_mul, ← ρ.map_mul]
    apply Units.ext
    apply Matrix.ext
    intro i j
    change (_root_.NativeTateCongruence.originalTateMatrix A ℓ b (φ * τ)).val i j =
      (_root_.NativeTateCongruence.originalTateMatrix A ℓ b (τ * φ)).val i j
    rw [_root_.NativeTateCongruence.original_matrix_entry,
      _root_.NativeTateCongruence.original_matrix_entry]
    exact congrArg (fun u : Module.End ℤ_[ℓ] (A.T ℓ) => b.repr (u (b j)) i) hAction
  have hFinite := hCommuting K (AlgebraicClosure K) G w ρ hContinuous φ hφ
    (Nat.card (IsLocalRing.ResidueField O)) hCong τ hτ hq hCommute hDensity
  let back : G → Module.End ℤ_[ℓ] (A.T ℓ) := fun g => (LinearMap.toMatrixAlgEquiv b).symm g.val
  have hBack (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
      back (ρ σ) = _root_.ReductSplit.galTΩ A ℓ σ := by
    apply (LinearMap.toMatrixAlgEquiv b).injective
    change (LinearMap.toMatrixAlgEquiv b)
        ((LinearMap.toMatrixAlgEquiv b).symm (_root_.NativeTateCongruence.originalTateMatrix A ℓ b σ).val) =
      (LinearMap.toMatrixAlgEquiv b) (_root_.ReductSplit.galTΩ A ℓ σ)
    rw [AlgEquiv.apply_symm_apply]
    apply Matrix.ext
    intro i j
    rw [_root_.NativeTateCongruence.original_matrix_entry, LinearMap.toMatrixAlgEquiv_apply]
    rfl
  have hOutput := hFinite.image back
  change (Set.range fun σ : {σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K //
      _root_.PkgI2.IsInertia w σ} => _root_.ReductSplit.galTΩ A ℓ σ.1).Finite
  apply hOutput.subset
  rintro f ⟨σ, rfl⟩
  exact ⟨ρ σ.1, ⟨σ.1, σ.2, rfl⟩, hBack σ.1⟩

end HDec.CMSerreTate.P1
