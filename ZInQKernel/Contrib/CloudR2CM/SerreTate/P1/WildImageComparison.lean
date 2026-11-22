import ZInQKernel.Contrib.CloudR2CM.SerreTate.FiniteInertiaStatements
import ZInQKernel.Contrib.CMSerreTateSupport.OriginalWildImageContracts

/-!
# Original integral wild-inertia comparison

The integral action and its literal wild-inertia domain are retained.
The finite-image result is obtained directly on the integral Tate module;
no reverse finiteness implication from rationalization is assumed.
-/

set_option autoImplicit false

noncomputable section

namespace HDec.CMSerreTate.P1

/-- The original integral representation is the original Tate action. -/
theorem originalTateRep_eq_galTΩ {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (A : _root_.PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (σ : Ω ≃ₐ[K] Ω) :
    _root_.NativeTateCongruence.originalTateRep A ℓ σ =
      _root_.ReductSplit.galTΩ A ℓ σ := rfl

/-- Finiteness on the original inertia-and-wild subtype, in the original
integral Tate action. No basis, rank or rational finite-image hypothesis
is added to the original number-field and valuation data. -/
theorem finiteWildInertiaImage_of_original {K Ω : Type} [Field K] [NumberField K]
    [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (O : ValuationSubring K) [IsDiscreteValuationRing O] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : O)) :
    HDec.CMSerreTate.FiniteWildInertiaImage A w ℓ := by
  change (Set.range fun σ : {σ : Ω ≃ₐ[K] Ω // _root_.PkgI2.IsInertia w σ ∧
      ∀ x : Ω, x ≠ 0 → w.valuation (σ x - x) < w.valuation x} =>
    _root_.NativeTateCongruence.originalTateRep A ℓ σ.1).Finite
  exact _root_.OriginalWildImageContracts.integral_inertia_wild O w hw A ℓ hℓ

end HDec.CMSerreTate.P1
