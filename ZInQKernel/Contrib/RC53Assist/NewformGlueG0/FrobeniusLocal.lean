import ZInQKernel.Contrib.Chebotarev.Exists
import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# Frobenius comparison and the transport of local factors

The absolute Galois group is the genuine Krull-topological group
`Gal(AlgebraicClosure ℚ/ℚ)`. Arithmetic Frobenius means the existing congruence
on the integral closure of the integers at a prime above a rational prime.
The density input is discharged by the proved Čebotarev theorem.

Equality of traces on these Frobenius elements gives equality of characters.
The semisimple isomorphism step is kept separate as the existing algebraic
proposition `GlueC10.BrauerNesbittChar0`; density alone does not prove it.
That proposition is proved in `BrauerNesbitt.lean`. It remains a parameter
here so that the invariant-space transport has an independent interface.

An isomorphism of representations identifies the inertia-fixed spaces and
conjugates Frobenius on them. Consequently the reversed characteristic
polynomials, the formal local Euler polynomials, agree. This proves the
linear-algebra part of the comparison needed with Carayol 1986, Théorème (A),
pp. 410–411 and §0.8, p. 411. It does not identify any arbitrary representation
with the elliptic curve's rational Tate module or the newform's representation.
-/

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.NewformGlueG0

open GlueC10 (GQ Qbar IsFrobAt)

/-- **DEFINITION**, using the genuine arithmetic-Frobenius predicate in
`HDecomp/C10/C10.lean`, §B: Frobenius elements outside a finite set of
rational primes, with all primes of the algebraic closure allowed. -/
def frobeniusElements (S : Finset ℕ) : Set GQ :=
  {g | ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ IsFrobAt g p}

/-- **PROVED**, by the Krull neighbourhood basis and the closed Čebotarev
existence theorem. Locators: `Contrib/Chebotarev/Exists.lean`,
`chebotarevExists_c10`, and `GlueC10.frobDense`.
The Frobenius elements remain dense after any finite set of primes is removed. -/
theorem frobeniusElements_dense (S : Finset ℕ) : Dense (frobeniusElements S) := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  obtain ⟨g, hg⟩ := hUne
  have hmem : (fun y : GQ => g * y) ⁻¹' U ∈ nhds (1 : GQ) := by
    apply (hU.preimage (continuous_const.mul continuous_id)).mem_nhds
    simpa using hg
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Qbar _).mp hmem
  obtain ⟨τ, p, hp, hpS, hτ, hEq⟩ :=
    GlueC10.frobDense ZInQ.Contrib.chebotarevExists_c10 S E hE g
  have hfix : g⁻¹ * τ ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change g⁻¹ (τ x) = x
    rw [hEq x hx]
    exact AlgEquiv.symm_apply_apply g x
  have hτU := hsub hfix
  change g * (g⁻¹ * τ) ∈ U at hτU
  rw [mul_inv_cancel_left] at hτU
  exact ⟨τ, hτU, ⟨p, hp, hpS, hτ⟩⟩

/-- **PROVED**, by continuity of matrix traces and the discharged Čebotarev
density. Locators: `GlueC10.continuous_trace`, `GlueC10.eq_of_eq_on_frob`.
This is equality of the characters of actual finite-dimensional continuous
Galois representations, not a semisimple-isomorphism assertion. -/
theorem trace_eq_of_frobenius {K V W ι κ : Type*} [Field K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (bV : Module.Basis ι K V) (bW : Module.Basis κ K W)
    (ρ : Representation K GQ V) (σ : Representation K GQ W)
    (hρc : Continuous fun g => LinearMap.toMatrix bV bV (ρ g))
    (hσc : Continuous fun g => LinearMap.toMatrix bW bW (σ g)) (S : Finset ℕ)
    (htr : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace K V (ρ g) = LinearMap.trace K W (σ g)) :
    ∀ g : GQ, LinearMap.trace K V (ρ g) = LinearMap.trace K W (σ g) := by
  have h := GlueC10.eq_of_eq_on_frob S
    (GlueC10.frobDense ZInQ.Contrib.chebotarevExists_c10 S) _ _
    (GlueC10.continuous_trace bV ρ hρc) (GlueC10.continuous_trace bW σ hσc) htr
  exact fun g => congrFun h g

/-- **PROVED**, from the independently stated Brauer–Nesbitt proposition and
the proved trace comparison. Locators: `GlueC10.BrauerNesbittChar0`, §A,
and `trace_eq_of_frobenius`. The algebraic Brauer–Nesbitt hypothesis is
explicit; no isomorphism is inferred from density alone. -/
theorem representationEquiv_of_BN_frobenius (hBN : GlueC10.BrauerNesbittChar0)
    (K V W ι κ : Type) [Field K] [CharZero K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (bV : Module.Basis ι K V) (bW : Module.Basis κ K W)
    (ρ : Representation K GQ V) (σ : Representation K GQ W)
    (hρc : Continuous fun g => LinearMap.toMatrix bV bV (ρ g))
    (hσc : Continuous fun g => LinearMap.toMatrix bW bW (σ g))
    (hρ : IsSemisimpleModule (MonoidAlgebra K GQ) ρ.asModule)
    (hσ : IsSemisimpleModule (MonoidAlgebra K GQ) σ.asModule) (S : Finset ℕ)
    (htr : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace K V (ρ g) = LinearMap.trace K W (σ g)) :
    Nonempty (Representation.Equiv ρ σ) := by
  obtain ⟨e⟩ := hBN K GQ V W ρ σ hρ hσ
    (trace_eq_of_frobenius bV bW ρ σ hρc hσc S htr)
  let f : Representation.IntertwiningMap ρ σ :=
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ).symm e.toLinearMap
  have hf : Function.Bijective f := by
    change Function.Bijective (fun x : V => e x)
    exact e.bijective
  exact ⟨f.ofBijective hf⟩

section LocalFactors

variable {K G V W : Type*} [Field K] [Group G]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- **DEFINITION**, the genuine invariant subspace of the restriction of a
representation to a subgroup. Locator: Mathlib `Representation.invariants`.
For an inertia subgroup this is the space entering the local Euler factor. -/
def fixedInertia (ρ : Representation K G V) (I : Subgroup G) : Submodule K V :=
  Representation.invariants (ρ.comp I.subtype)

/-- **PROVED**, by the defining equivariance of an isomorphism of
representations. Locator: Mathlib `IntertwiningMap.isIntertwining`.
Invariant vectors remain invariant under an equivariant isomorphism. -/
theorem map_mem_fixedInertia {ρ : Representation K G V} {σ : Representation K G W}
    (e : Representation.Equiv ρ σ) (I : Subgroup G) {v : V}
    (hv : v ∈ fixedInertia ρ I) : e v ∈ fixedInertia σ I := by
  change ∀ i : I, ρ (i : G) v = v at hv
  change ∀ i : I, σ (i : G) (e v) = e v
  intro i
  have h : e (ρ (i : G) v) = σ (i : G) (e v) :=
    Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap (i : G) v
  exact h.symm.trans (congrArg (fun x => e x) (hv i))

/-- **DEFINITION WITH PROVED INVERSE**, the induced linear equivalence on
inertia-fixed spaces. Locator: `map_mem_fixedInertia`; both directions use
the given representation isomorphism, not a new local comparison input. -/
def fixedInertiaEquiv {ρ : Representation K G V} {σ : Representation K G W}
    (e : Representation.Equiv ρ σ) (I : Subgroup G) :
    fixedInertia ρ I ≃ₗ[K] fixedInertia σ I where
  toFun v := ⟨e v.1, map_mem_fixedInertia e I v.2⟩
  invFun w := ⟨e.symm w.1, map_mem_fixedInertia e.symm I w.2⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v.1)
  right_inv w := Subtype.ext (e.apply_symm_apply w.1)
  map_add' v w := Subtype.ext (map_add e v.1 w.1)
  map_smul' a v := Subtype.ext (map_smul e a v.1)

/-- **PROVED**, by conjugating an inertia element by Frobenius.
Locator: the definition of `fixedInertia`. Only the displayed normalization
condition is needed; inertia need not be normal in the entire global group. -/
theorem fixedInertia_stable (ρ : Representation K G V) (I : Subgroup G)
    (g : G) (hg : ∀ i ∈ I, g⁻¹ * i * g ∈ I) {v : V}
    (hv : v ∈ fixedInertia ρ I) : ρ g v ∈ fixedInertia ρ I := by
  change ∀ i : I, ρ (i : G) v = v at hv
  change ∀ i : I, ρ (i : G) (ρ g v) = ρ g v
  intro i
  have hi : g⁻¹ * (i : G) * g ∈ I := hg i.1 i.2
  have hfixed := hv ⟨g⁻¹ * (i : G) * g, hi⟩
  calc
    ρ (i : G) (ρ g v) = ρ ((i : G) * g) v := by rw [map_mul, Module.End.mul_apply]
    _ = ρ (g * (g⁻¹ * (i : G) * g)) v := by simp [mul_assoc]
    _ = ρ g (ρ (g⁻¹ * (i : G) * g) v) := by rw [map_mul, Module.End.mul_apply]
    _ = ρ g v := congrArg (ρ g) hfixed

/-- **DEFINITION WITH PROVED STABILITY**, Frobenius acting on the actual
inertia-fixed subspace. Locator: `fixedInertia_stable`. -/
def inertiaFrobenius (ρ : Representation K G V) (I : Subgroup G)
    (g : G) (hg : ∀ i ∈ I, g⁻¹ * i * g ∈ I) : Module.End K (fixedInertia ρ I) where
  toFun v := ⟨ρ g v.1, fixedInertia_stable ρ I g hg v.2⟩
  map_add' v w := Subtype.ext (map_add (ρ g) v.1 w.1)
  map_smul' a v := Subtype.ext (map_smul (ρ g) a v.1)

/-- **PROVED**, by equivariance on the inertia-fixed spaces; locator:
`fixedInertiaEquiv`. The restricted Frobenius endomorphisms are genuinely
conjugate, not merely equal on their traces. -/
theorem inertiaFrobenius_conj {ρ : Representation K G V} {σ : Representation K G W}
    (e : Representation.Equiv ρ σ) (I : Subgroup G)
    (g : G) (hg : ∀ i ∈ I, g⁻¹ * i * g ∈ I) :
    (fixedInertiaEquiv e I).conj (inertiaFrobenius ρ I g hg) =
      inertiaFrobenius σ I g hg := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change e (ρ g (e.symm v.1)) = σ g v.1
  have h : e (ρ g (e.symm v.1)) = σ g (e (e.symm v.1)) :=
    Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g (e.symm v.1)
  exact h.trans (congrArg (σ g) (e.apply_symm_apply v.1))

/-- **DEFINITION**, the formal local Euler polynomial, the reversed
characteristic polynomial of Frobenius on inertia invariants. Locator:
Carayol 1986, §0.5, p. 410, and Théorème (A), pp. 410–411; the group,
subgroup, and Frobenius here are supplied explicitly. -/
def inertiaEulerPolynomial [FiniteDimensional K V]
    (ρ : Representation K G V) (I : Subgroup G)
    (g : G) (hg : ∀ i ∈ I, g⁻¹ * i * g ∈ I) : Polynomial K :=
  (LinearMap.charpoly (inertiaFrobenius ρ I g hg)).reverse

/-- **PROVED**, by conjugacy of the actual restricted Frobenius maps.
Locator: Mathlib `LinearEquiv.charpoly_conj`, and `inertiaFrobenius_conj`.
Thus a representation comparison transports all local Euler polynomials,
including ramified primes and zero-dimensional inertia-fixed spaces. -/
theorem inertiaEulerPolynomial_eq_of_equiv [FiniteDimensional K V] [FiniteDimensional K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (e : Representation.Equiv ρ σ) (I : Subgroup G)
    (g : G) (hg : ∀ i ∈ I, g⁻¹ * i * g ∈ I) :
    inertiaEulerPolynomial ρ I g hg = inertiaEulerPolynomial σ I g hg := by
  unfold inertiaEulerPolynomial
  rw [← inertiaFrobenius_conj e I g hg, LinearEquiv.charpoly_conj]

end LocalFactors

/-- **PROVED**, from the explicit algebraic Brauer–Nesbitt input and the
proved density and invariant-space transport. Locators: Carayol 1986,
Théorème (A), pp. 410–411, §0.8, p. 411; `representationEquiv_of_BN_frobenius`
and `inertiaEulerPolynomial_eq_of_equiv`.
This is the local-factor consequence of the Galois comparison, without
assuming equality of local factors or equality of all newform coefficients. -/
theorem localFactors_eq_of_BN_frobenius (hBN : GlueC10.BrauerNesbittChar0)
    (K V W ι κ : Type) [Field K] [CharZero K]
    [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (bV : Module.Basis ι K V) (bW : Module.Basis κ K W)
    (ρ : Representation K GQ V) (σ : Representation K GQ W)
    (hρc : Continuous fun g => LinearMap.toMatrix bV bV (ρ g))
    (hσc : Continuous fun g => LinearMap.toMatrix bW bW (σ g))
    (hρ : IsSemisimpleModule (MonoidAlgebra K GQ) ρ.asModule)
    (hσ : IsSemisimpleModule (MonoidAlgebra K GQ) σ.asModule) (S : Finset ℕ)
    (htr : ∀ g p, p.Prime → p ∉ S → IsFrobAt g p →
      LinearMap.trace K V (ρ g) = LinearMap.trace K W (σ g)) :
    ∀ (I : Subgroup GQ) (g : GQ) (hg : ∀ i ∈ I, g⁻¹ * i * g ∈ I),
      inertiaEulerPolynomial ρ I g hg = inertiaEulerPolynomial σ I g hg := by
  obtain ⟨e⟩ := representationEquiv_of_BN_frobenius hBN K V W ι κ bV bW ρ σ
    hρc hσc hρ hσ S htr
  exact fun I g hg => inertiaEulerPolynomial_eq_of_equiv e I g hg

end ZInQ.Contrib.RC53Assist.NewformGlueG0
