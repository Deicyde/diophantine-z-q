import ZInQKernel.Contrib.CloudR2CM.SerreTate.FiniteInertiaStatements
import ProcyclicV002
import BindingObjectsV001

/-!
# Arithmetic supplier outputs and the CM commutation obligation

These are statement interfaces, not proofs. Generic procyclicity does not
choose a generator of the actual tame quotient. Frobenius conjugation is
stated modulo the original wild inertia, not as exact equality on the Tate
module. The CM commutation obligation concerns the whole Galois image; mere
commutativity of the inertia image does not suffice.
-/

set_option autoImplicit false

noncomputable section

open Topology

namespace HDec.CMSerreTate

/-- The literal conclusion of the generic compact procyclic supplier.
Its compactness, open-normal-basis and quotient-cyclicity inputs must be
provided for the actual group before this output can be used there. -/
def ProcyclicSupplierOutput (H : Type*) [Group H] [TopologicalSpace H] : Prop :=
  ∃ g : H, Dense (Subgroup.zpowers g : Set H)

/-- Decomposition membership and the original residue Frobenius congruence,
in the literal predicates consumed by the tame-character supplier. -/
def FrobeniusResidueWitness {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (w : ValuationSubring Ω) (q : ℕ) (φ : Ω ≃ₐ[K] Ω) : Prop :=
  φ ∈ w.decompositionSubgroup K ∧
    ∀ u : Ω, u ∈ w → _root_.WildTameCharacter.Cong w (φ u) (u ^ q)

/-- The actual Frobenius-lift output at the specified residue cardinality. -/
def FrobeniusSupplierOutput {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (w : ValuationSubring Ω) (q : ℕ) : Prop :=
  ∃ φ : Ω ≃ₐ[K] Ω, FrobeniusResidueWitness w q φ

/-- The tame-character supplier's literal conclusion for every original
inertia element. It is a wild congruence, not an equality of operators. -/
def FrobeniusWildRelation {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (w : ValuationSubring Ω) (q : ℕ) (φ : Ω ≃ₐ[K] Ω) : Prop :=
  ∀ σ : Ω ≃ₐ[K] Ω, _root_.PkgI2.IsInertia w σ →
    _root_.WildTameCharacter.IsWild w ((φ * σ * φ⁻¹)⁻¹ * σ ^ q)

/-- The stronger literal wild-inertia conclusion: the produced commutator
is itself in original inertia and satisfies the original wild predicate. -/
def FrobeniusInertiaWildRelation {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (w : ValuationSubring Ω) (q : ℕ) (φ : Ω ≃ₐ[K] Ω) : Prop :=
  ∀ σ : Ω ≃ₐ[K] Ω, _root_.PkgI2.IsInertia w σ →
    _root_.PkgI2.IsInertia w ((φ * σ * φ⁻¹)⁻¹ * σ ^ q) ∧
      _root_.SZRaynaud.IsWildInertia w ((φ * σ * φ⁻¹)⁻¹ * σ ^ q)

/-- Commutativity of the whole decomposition image, including Frobenius
and every inertia element, under the original Tate action. -/
def DecompositionImageAbelian {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
    (A : _root_.PkgI3.AbVar K) (w : ValuationSubring Ω)
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ w.decompositionSubgroup K →
    ∀ τ : Ω ≃ₐ[K] Ω, τ ∈ w.decompositionSubgroup K →
      Commute (_root_.ReductSplit.galTΩ A ℓ σ) (_root_.ReductSplit.galTΩ A ℓ τ)

/-- Commutativity of the whole Galois image on the original Tate module. -/
def GaloisImageAbelian {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ σ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
    Commute (_root_.ReductSplit.galTΩ A ℓ σ) (_root_.ReductSplit.galTΩ A ℓ τ)

/-- The CM representation obligation used within P1. It concerns the whole
Galois image, not only inertia; its intended proof constructs the faithful
rank-one action of the commutative quadratic tensor algebra on the rational
Tate module. That tensor algebra is not assumed to be a field. -/
def CMGaloisImageAbelian : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : _root_.PkgI3.AbVar K),
    A.dim = 1 →
    ∀ (k : Type) [Field k] [NumberField k] (R : Subring k),
      HDec.CMBranch.IsImagQuadOrder k R → BaseDefinedCM A R →
      ∀ (ℓ : ℕ) [Fact ℓ.Prime], GaloisImageAbelian A ℓ

end HDec.CMSerreTate
