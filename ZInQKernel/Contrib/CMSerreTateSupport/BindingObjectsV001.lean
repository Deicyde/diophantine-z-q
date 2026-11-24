import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CMSerreTateSupport.TameCharacterV005
import ZInQKernel.Contrib.CMSerreTateSupport.TameCyclicV002

/-!
# The tame-character congruences for the kernel's inertia predicate

The kernel's `PkgI2.IsInertia w σ` is, by definition, membership of `σ` in Mathlib's inertia
subgroup of `w`. On an algebraic extension (for example an algebraic closure) it yields the
inertia conditions, the Frobenius congruence and the commutator congruence. Here `IsWild` is
the strict-displacement condition `v(σ x − x) < v(x)` for all `x ≠ 0`.
-/

noncomputable section
set_option autoImplicit false

namespace WildTameBinding

open WildTameCharacter

variable {K L : Type} [Field K] [Field L] [Algebra K L]

theorem inertia_conditions_of_isInertia [Algebra.IsAlgebraic K L] {w : ValuationSubring L}
    {σ : L ≃ₐ[K] L} (h : PkgI2.IsInertia w σ) :
    Preserves w σ ∧ ∀ u : L, w.valuation u = 1 → Cong w (σ u) u :=
  inertia_conditions h

theorem isWild_frobenius_of_isInertia [Algebra.IsAlgebraic K L] {w : ValuationSubring L}
    {σ φ : L ≃ₐ[K] L} (q : ℕ) (h : PkgI2.IsInertia w σ)
    (hφ : φ ∈ w.decompositionSubgroup K) (hφq : ∀ u : L, u ∈ w → Cong w (φ u) (u ^ q)) :
    IsWild w ((φ * σ * φ⁻¹)⁻¹ * σ ^ q) :=
  isWild_frobenius_of_inertia q h hφ hφq

theorem isWild_commutator_of_isInertia [Algebra.IsAlgebraic K L] {w : ValuationSubring L}
    {σ τ : L ≃ₐ[K] L} (hσ : PkgI2.IsInertia w σ) (hτ : PkgI2.IsInertia w τ) :
    IsWild w ((τ * σ)⁻¹ * (σ * τ)) :=
  isWild_commutator_of_inertia hσ hτ

/-- The literal setting: an algebraic closure is algebraic. -/
theorem isAlgebraic_of_isAlgClosure (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    Algebra.IsAlgebraic K Ω :=
  IsAlgClosure.isAlgebraic

/-- The Frobenius congruence in the exact objects of the leaf: `Ω` an algebraic closure of `K`,
`σ` with the kernel's `IsInertia`. -/
theorem isWild_frobenius_algClosure (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {w : ValuationSubring Ω} {σ φ : Ω ≃ₐ[K] Ω} (q : ℕ) (h : PkgI2.IsInertia w σ)
    (hφ : φ ∈ w.decompositionSubgroup K) (hφq : ∀ u : Ω, u ∈ w → Cong w (φ u) (u ^ q)) :
    IsWild w ((φ * σ * φ⁻¹)⁻¹ * σ ^ q) :=
  haveI := isAlgebraic_of_isAlgClosure (K := K) Ω
  isWild_frobenius_of_inertia q h hφ hφq

end WildTameBinding
