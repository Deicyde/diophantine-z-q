import ZInQKernel.Contrib.CloudR2CM.SerreTate.FiniteInertiaStatements
import ZInQKernel.Contrib.AbVarBC.Points

/-!
# P2: Serre's lemma and the choice of the field `L₁`

Statements only; they supply no proofs.

* `InertiaTrivialOnTate`: inertia at `w` acts trivially on `T_ℓ(A)`, the predicate carried from
  P2 to P3. It uses the project's objects: `PkgI2.IsInertia` (Mathlib's inertia subgroup of the
  valuation ring `w`), `ReductSplit.TΩ` (`T_ℓ(A) = lim A(Ω)[ℓⁿ]`) and `ReductSplit.galTΩ` (the action
  of `σ ∈ Aut_K(Ω)` on it), as in the leaf `SZRaynaud.ElliotWildInertiaTrivial`.
* `SerreLemmaTate` (**Serre's lemma**): a ℤ_ℓ-linear endomorphism of finite order of a Tate module
  `T_ℓ(M) = lim M[ℓⁿ]` that is congruent to `1` modulo `ℓ^k` with `ℓ^k ≥ 3` is the identity
  (Serre, *Rigidité du foncteur de Jacobi d'échelon n ≥ 3*, Sém. Cartan 13 (1960/61), appendix;
  numbers UNVERIFIED). The Tate module is torsion-free and `ℓ`-adically separated by construction,
  so no freeness of `T_ℓ` is assumed.
* `P2InertiaRigidity` (one place): a finite inertia image (the P1 output `FiniteInertiaImage`)
  together with inertia fixing `A(Ω)[ℓ^k]`, `ℓ^k ≥ 3`, makes inertia trivial on `T_ℓ(A)`. Its proof
  is `SerreLemmaTate` applied to each `galTΩ σ`: finite order because the image is finite and closed
  under composition, congruent to `1` modulo `ℓ^k` because the kernel of `T_ℓ(A) → A(Ω)[ℓ^k]` is
  `ℓ^k T_ℓ(A)`.
* `P2TorsionField` (the choice of `L₁`): for a finite extension `L'/L` and two prime powers
  `ℓ₁^k₁`, `ℓ₂^k₂`, a finite extension `L₁ ⊇ L'` of `L` over which `A[ℓ₁^k₁]` and `A[ℓ₂^k₂]` are
  rational. With two distinct primes and `ℓᵢ^kᵢ ≥ 3` (the route takes `2²` and `3`), every finite
  place of `L₁` has a residue characteristic different from some `ℓᵢ`, and that `ℓᵢ` is used there.
-/

set_option autoImplicit false

noncomputable section

open scoped CategoryTheory.MonObj

namespace HDec.CMSerreTate

/-- Inertia at `w` acts trivially on `T_ℓ(A)`: every `σ` in the inertia group of `w` fixes every
element of `T_ℓ(A) = lim A(Ω)[ℓⁿ]` under the original Tate-module action. -/
def InertiaTrivialOnTate {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    {Ω : Type} [Field Ω] [Algebra K Ω] (w : ValuationSubring Ω) (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  ∀ σ : Ω ≃ₐ[K] Ω, _root_.PkgI2.IsInertia w σ →
    ∀ t : _root_.ReductSplit.TΩ A Ω ℓ, _root_.ReductSplit.galTΩ A ℓ σ t = t

/-- **Serre's lemma, Tate-module form.** A ℤ_ℓ-linear endomorphism `f` of `T_ℓ(M)` with `f ^ n = 1`
for some `n > 0` and `f ≡ 1` modulo `ℓ^k`, `ℓ^k ≥ 3`, is the identity. -/
def SerreLemmaTate : Prop :=
  ∀ (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ), 3 ≤ ℓ ^ k →
    ∀ (M : Type) [AddCommGroup M]
      (f : _root_.PkgI3.Tate.T ℓ M →ₗ[ℤ_[ℓ]] _root_.PkgI3.Tate.T ℓ M),
      (∃ n : ℕ, 0 < n ∧ f ^ n = 1) →
      (∀ x : _root_.PkgI3.Tate.T ℓ M, ∃ y : _root_.PkgI3.Tate.T ℓ M,
        f x - x = ((ℓ : ℤ_[ℓ]) ^ k) • y) →
      f = 1

/-- **P2, rigidity at one place.** If the image of inertia at `w` on `T_ℓ(A)` is finite and inertia
fixes every point of `A(Ω)` killed by `ℓ^k`, with `ℓ^k ≥ 3`, then inertia acts trivially on
`T_ℓ(A)`. -/
def P2InertiaRigidity : Prop :=
  ∀ (K : Type) [Field K] (A : _root_.PkgI3.AbVar K) (Ω : Type) [Field Ω] [Algebra K Ω]
    (w : ValuationSubring Ω) (ℓ : ℕ) [Fact ℓ.Prime] (k : ℕ), 3 ≤ ℓ ^ k →
    FiniteInertiaImage A w ℓ →
    (∀ σ : Ω ≃ₐ[K] Ω, _root_.PkgI2.IsInertia w σ →
      ∀ x : A.Pt Ω, x ^ (ℓ ^ k) = 1 → A.galAct σ x = x) →
    InertiaTrivialOnTate A w ℓ

/-- **P2, the choice of `L₁`.** For a finite extension `L'/L` and prime powers `ℓ₁^k₁`, `ℓ₂^k₂`,
there is a finite extension `L₁` of `L` receiving `L'` over `L` such that every point of
`A_{L₁}(L̄₁)` killed by `ℓ₁^k₁` or by `ℓ₂^k₂` comes from an `L₁`-point. -/
def P2TorsionField : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (A : _root_.PkgI3.AbVar L)
    (L' : Type) [Field L'] [Algebra L L'] [FiniteDimensional L L']
    (ℓ₁ ℓ₂ k₁ k₂ : ℕ), ℓ₁.Prime → ℓ₂.Prime →
    ∃ (L₁ : Type) (_ : Field L₁) (_ : NumberField L₁) (_ : Algebra L L₁)
      (_ : FiniteDimensional L L₁),
      Nonempty (L' →ₐ[L] L₁) ∧
      ∀ m : ℕ, (m = ℓ₁ ^ k₁ ∨ m = ℓ₂ ^ k₂) →
        ∀ x : (A.baseChange L₁).Pt (AlgebraicClosure L₁), x ^ m = 1 →
          ∃ y : (A.baseChange L₁).Pt L₁,
            _root_.ZInQ.Contrib.AbVarBC.extPt (A.baseChange L₁)
              (Algebra.ofId L₁ (AlgebraicClosure L₁)) y = x

/-- **P2**: rigidity at each place and the choice of `L₁`. -/
def P2SerreChoice : Prop :=
  P2InertiaRigidity ∧ P2TorsionField

end HDec.CMSerreTate
