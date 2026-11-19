import ZInQKernel.Contrib.OneProof.CMBranch
import ZInQKernel.Contrib.OneProof.SZRaynaud

/-!
# Finite inertia interfaces for the CM potential-good route

These definitions state obligations; they do not supply proofs of them.
The endomorphism-ring hypothesis below is over the field of definition,
not merely over its algebraic closure. The inertia action is the original
Tate-module action, with the project valuation-subring inertia predicate.
-/

set_option autoImplicit false

noncomputable section

namespace HDec.CMSerreTate

/-- CM endomorphisms defined over the actual ground field, with the given
order as their endomorphism ring. This is an output condition for descent
of geometric endomorphisms, not a replacement for geometric CM. -/
def BaseDefinedCM {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    {k : Type} [Field k] (R : Subring k) : Prop :=
  Nonempty (_root_.PkgI3.AbVar.End A ≃+* R)

/-- The actual inertia image on the original integral Tate module. -/
def FiniteInertiaImage {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  (Set.range fun σ : {σ : Ω ≃ₐ[K] Ω // _root_.PkgI2.IsInertia w σ} =>
    _root_.ReductSplit.galTΩ A ℓ σ.1).Finite

/-- The actual wild-inertia image, with both inertia membership and the
original strict valuation-displacement predicate. -/
def FiniteWildInertiaImage {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω)
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  (Set.range fun σ : {σ : Ω ≃ₐ[K] Ω //
      _root_.PkgI2.IsInertia w σ ∧ _root_.SZRaynaud.IsWildInertia w σ} =>
    _root_.ReductSplit.galTΩ A ℓ σ.1).Finite

/-- The P1 obligation: a base-defined CM elliptic curve has finite inertia
image at every finite-residue discrete valuation, for every prime invertible
there. No prime-to-conductor restriction is imposed. -/
def P1FiniteInertia : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : _root_.PkgI3.AbVar K),
    A.dim = 1 →
    ∀ (k : Type) [Field k] [NumberField k] (R : Subring k),
      HDec.CMBranch.IsImagQuadOrder k R → BaseDefinedCM A R →
      ∀ (O : ValuationSubring K) [IsDiscreteValuationRing O]
        [Finite (IsLocalRing.ResidueField O)]
        (w : ValuationSubring (AlgebraicClosure K)),
        w.comap (algebraMap K (AlgebraicClosure K)) = O →
        ∀ (ℓ : ℕ) [Fact ℓ.Prime], IsUnit (ℓ : O) →
          FiniteInertiaImage A w ℓ

end HDec.CMSerreTate
