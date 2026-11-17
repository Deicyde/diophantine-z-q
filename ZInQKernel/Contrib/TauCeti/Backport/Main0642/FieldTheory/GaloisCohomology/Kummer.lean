/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 0642eae29e0a, module
-- TauCeti.FieldTheory.GaloisCohomology.Kummer), Apache-2.0: declarations of that module absent from its commit-5a01f5fe version, which
-- is vendored as `ZInQKernel.Contrib.TauCeti.FieldTheory.GaloisCohomology.Kummer` (task selmer-2infty).
-- Modified for the Z-in-Q kernel: declarations already in the vendored module removed; imports rewritten.
module

public import ZInQKernel.Contrib.TauCeti.FieldTheory.GaloisCohomology.Kummer
public import ZInQKernel.Contrib.TauCeti.Algebra.Group.PowerClassGroup.Basic
public import ZInQKernel.Contrib.TauCeti.Algebra.GroupWithZero.Units.Basic
public import ZInQKernel.Contrib.TauCeti.Backport.Main0642.FieldTheory.Galois.AbsoluteGaloisGroup.Norm
public import ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Map
public import ZInQKernel.Contrib.TauCeti.FieldTheory.GaloisCohomology.Hilbert90
public import ZInQKernel.Contrib.TauCeti.Backport.Main0642.FieldTheory.GaloisCohomology.Units.CoeffMap
public import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.DeltaNaturality
public import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.LongExact
public import ZInQKernel.Contrib.TauCeti.RingTheory.Norm.Units
public import ZInQKernel.Contrib.TauCeti.Topology.Algebra.ConstMulAction

/-!
# The Kummer map `Kˣ → H¹(G_K, μₙ)` and the Kummer isomorphism

Let `K` be a field, `Kˢ` a separable closure, `G_K = AbsoluteGaloisGroup K`, and `n` a natural
number invertible in `K`. The Kummer sequence

```text
1 ⟶ μₙ ⟶ (Kˢ)ˣ ⟶ (Kˢ)ˣ ⟶ 1
```

of discrete `G_K`-modules is `TauCeti.kummerShortExact`; its degree-zero connecting map, read
through the identification `TauCeti.baseUnitsEquivInvariants` of `H⁰(G_K, (Kˢ)ˣ)` with `Kˣ`, is
the **Kummer map** `Kˣ → H¹(G_K, μₙ)`. This file constructs it, computes it on cocycles, identifies
its kernel, and proves that it induces the Kummer isomorphism `Kˣ ⧸ (Kˣ)ⁿ ≃ H¹(G_K, μₙ)`.

The computation is the classical one. Choose an `n`th root `α ∈ (Kˢ)ˣ` of `a ∈ Kˣ`; then
`g ↦ g α / α` takes values in `μₙ`, because raising it to the `n` gives `g a / a = 1`, and it is a
continuous `1`-cocycle, because its image in `(Kˢ)ˣ` is the coboundary `d⁰ α`. Its class is the
Kummer class of `a`. The class does not depend on the choice of root: two roots differ by an
element `ζ` of `μₙ`, and the two cocycles differ by the coboundary `d⁰ ζ`. That independence is
proved directly, with no hypothesis on `n`, so it is available for any `a` that happens to have a
root.

The kernel is `(Kˣ)ⁿ`. This is exactness of the long exact sequence at `H⁰(G_K, (Kˢ)ˣ)` —
`explicitLongExact_H0C` — together with the commuting square
`TauCeti.explicitCoeff0_baseUnitsEquivInvariants`, which says that the `n`th power map on the
invariants of `(Kˢ)ˣ` is the `n`th power map of `Kˣ`. So the Kummer map descends to an
**injection** of the power-class group `Kˣ ⧸ (Kˣ)ⁿ` into `H¹(G_K, μₙ)`.

The Kummer map is **surjective**. This is exactness of the same sequence at `H¹(G_K, μₙ)` —
`explicitLongExact_H1A` — together with Hilbert 90, `H¹(G_K, (Kˢ)ˣ) = 0`
(`TauCeti.subsingleton_H1_unitsCoeff`): every class of `H¹(G_K, μₙ)` dies in `H¹(G_K, (Kˢ)ˣ)` and so
is a connecting image. Injectivity on power classes and surjectivity together give the **Kummer
isomorphism** `TauCeti.kummerIso`.

The Kummer isomorphism is **natural in the field** for restriction. A `K`-embedding
`σ : L →ₐ[K] Kˢ` identifies `Lˢ` with `Kˢ` and `G_L` with the subgroup of `G_K` fixing `σ(L)`;
restricting the Kummer cocycle `g ↦ g α / α` of `a ∈ Kˣ` to that subgroup and transporting it to
`G_L` gives the Kummer cocycle of the image of `a` in `Lˣ`, with the transported root. So
restriction on `H¹(·, μₙ)` corresponds to the map `Kˣ ⧸ (Kˣ)ⁿ → Lˣ ⧸ (Lˣ)ⁿ` of power classes. No
finiteness of `L/K` is used.

For a **finite** `L/K` the subgroup fixing `σ(L)` is open of index `[L : K]`, so it carries a
corestriction, and the second square of the functoriality says that corestriction
`H¹(G_L, μₙ) → H¹(G_K, μₙ)` corresponds to the norm `Lˣ ⧸ (Lˣ)ⁿ → Kˣ ⧸ (Kˣ)ⁿ`. In degree zero,
corestriction on the invariant `σ b` of the fixing subgroup is the product of the conjugates of
`σ b`, that is `N_{L/K} b`.

## Main definitions

* `TauCeti.kummerCocycle`: the cocycle `g ↦ g α / α` attached to a choice of `n`th root, and
  `TauCeti.kummerCocycleClass` its class in `H¹(G_K, μₙ)`.
* `TauCeti.kummerMap`: the multiplicative Kummer map
  `Kˣ →* Multiplicative (H¹(G_K, μₙ))`.
* `TauCeti.kummerClassMap`: the induced map on the power classes `Kˣ ⧸ (Kˣ)ⁿ`.
* `TauCeti.kummerIso`: the Kummer isomorphism `Kˣ ⧸ (Kˣ)ⁿ ≃* H¹(G_K, μₙ)`.
* `TauCeti.kummerIsoTransport`: the Kummer isomorphism after an equivariant identification of
  the roots of unity with another discrete coefficient module.
* `TauCeti.kummerCoeffPow`: the power map `μₙ → μₘ`, `ζ ↦ ζ ^ (n / m)`, for `m ∣ n`.
* `TauCeti.kummerRes`: restriction `H¹(G_K, μₙ) → H¹(G_L, μₙ)` along a `K`-embedding
  `σ : L →ₐ[K] Kˢ`, with its coefficient identification `TauCeti.kummerCoeffMap`.
* `TauCeti.kummerCoeffBaseChange`: transport of roots-of-unity coefficients along an embedding
  of separable closures over an arbitrary field extension.
* `TauCeti.kummerCor`: corestriction `H¹(G_L, μₙ) → H¹(G_K, μₙ)` along a `K`-embedding of a
  finite extension, with its coefficient identifications `TauCeti.kummerCoeffMapSymm` and
  `TauCeti.unitsCoeffMapSymm` (`TauCeti.FieldTheory.GaloisCohomology.Units.CoeffMap`).

## Main results

* `TauCeti.kummerCocycle_mem_Z1`: `g ↦ g α / α` is a continuous `1`-cocycle.
* `TauCeti.kummerCocycleClass_def`: the cocycle class is the class of its named cocycle.
* `TauCeti.kummerCocycleClass_congr`: independence of the choice of `n`th root.
* `TauCeti.kummerMap_eq_kummerCocycleClass`: the Kummer class of `a` is the class of
  `g ↦ g α / α`.
* `TauCeti.ker_kummerMap`: the kernel of the Kummer map is `(Kˣ)ⁿ`, with
  `TauCeti.kummerMap_eq_one_iff` the pointwise form.
* `TauCeti.kummerClassMap_injective`: `Kˣ ⧸ (Kˣ)ⁿ` injects into `H¹(G_K, μₙ)`.
* `TauCeti.kummerMap_surjective`: every class of `H¹(G_K, μₙ)` is a Kummer class.
* `TauCeti.finite_H1_kummerCoeff`: `H¹(G_K, μₙ)` is finite when `Kˣ ⧸ (Kˣ)ⁿ` is.
* `TauCeti.finite_H1_of_isPrimitiveRoot_of_natCard_eq`: the same for every cyclic trivial module of
  order `n` over a group isomorphic to `G_K`, when `K` contains the `n`th roots of unity.
* `TauCeti.explicitCoeff1_kummerCoeffPow_kummerMap`: the power map `μₙ → μₘ` sends the Kummer
  class of `a` at level `n` to its Kummer class at level `m`, and
  `TauCeti.explicitCoeff1_kummerCoeffPow_surjective`: it is surjective on `H¹` when `n` is
  invertible in `K`.
* `TauCeti.explicitIso_kummerMap`: the explicit and canonical Kummer maps agree under the
  degree-one comparison isomorphism.
* `TauCeti.explicitMap1_kummerMap`: pullback along an arbitrary field extension carries the
  Kummer class of a unit to the Kummer class of its image, and `TauCeti.explicitMap1_kummerIso` is
  the same statement on power classes.
* `TauCeti.kummerIso_res`: the Kummer isomorphism is natural for restriction along a field
  extension, restriction corresponding to the map of power classes `Kˣ ⧸ (Kˣ)ⁿ → Lˣ ⧸ (Lˣ)ⁿ`;
  `TauCeti.kummerRes_kummerMap` is the same statement on units.
* `TauCeti.explicitCor0_embeddedUnitsInvariants`: degree-zero corestriction on the invariants of
  `(Kˢ)ˣ` is the norm of `L/K`.
* `TauCeti.kummerIso_norm`: for a finite `L/K`, corestriction corresponds to the map of power
  classes `Lˣ ⧸ (Lˣ)ⁿ → Kˣ ⧸ (Kˣ)ⁿ` induced by the norm; `TauCeti.kummerCor_kummerMap` is the
  same statement on units.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (6.2.1) and the
  display following it.
-/

public section

noncomputable section

namespace TauCeti

open ContCohomology

variable {K : Type*} [Field K] {n : ℕ}

/-! ### The cocycle attached to an `n`th root

Nothing in this section needs `n` to be invertible in `K`: the input is a chosen `n`th root of the
given unit, and invertibility of `n` is only what produces one. -/

variable {a : Kˣ} {α β : (SeparableClosure K)ˣ}

/-! ### The Kummer map and its kernel -/

variable (K n)

/-- The additive shape of the Kummer connecting homomorphism. This is an implementation detail
of `TauCeti.kummerMap`, whose public evaluation lemma `TauCeti.kummerMap_apply` states the same
equation in terms of `explicitDelta0`. -/
private def kummerMapAdd (hn : IsUnit (n : K)) :
    Additive Kˣ →+ H1 (AbsoluteGaloisGroup K) (KummerCoeff K n) :=
  (kummerShortExact K n hn).explicitDelta0.comp (baseUnitsEquivInvariants K).toAddMonoidHom

/-- The defining equation of the implementation helper `kummerMapAdd`. -/
private theorem kummerMapAdd_apply (hn : IsUnit (n : K)) (c : Additive Kˣ) :
    kummerMapAdd K n hn c =
      (kummerShortExact K n hn).explicitDelta0 (baseUnitsEquivInvariants K c) :=
  (rfl)

variable {K n}

/-- The additive form of `TauCeti.ker_kummerMap`. Exactness at `H⁰(G_K, (Kˢ)ˣ)` says the kernel
of `δ⁰` is the image of the `n`th power map on invariants, and
`TauCeti.explicitCoeff0_baseUnitsEquivInvariants` reads that image off in `Kˣ`. -/
private theorem ker_kummerMapAdd (hn : IsUnit (n : K)) :
    (kummerMapAdd K n hn).ker = (powerSubgroup Kˣ n).toAddSubgroup := by
  have hker : ∀ c : Additive Kˣ, kummerMapAdd K n hn c = 0 ↔
      baseUnitsEquivInvariants K c ∈ (explicitCoeff0 (AbsoluteGaloisGroup K) (UnitsCoeff K)
        (kummerShortExact K n hn).projDistribMulActionHom).range := fun c => by
    rw [(kummerShortExact K n hn).explicitLongExact_H0C]
    exact (AddMonoidHom.mem_ker (f := (kummerShortExact K n hn).explicitDelta0)).symm
  ext c
  rw [AddMonoidHom.mem_ker, hker, Additive.mem_toAddSubgroup, mem_powerSubgroup_iff]
  refine ⟨fun ⟨u, hu⟩ => ?_, fun ⟨v, hv⟩ => ⟨baseUnitsEquivInvariants K (Additive.ofMul v), ?_⟩⟩
  · obtain ⟨d, rfl⟩ := (baseUnitsEquivInvariants K).surjective u
    rw [explicitCoeff0_baseUnitsEquivInvariants] at hu
    exact ⟨d.toMul, congrArg Additive.toMul ((baseUnitsEquivInvariants K).injective hu)⟩
  · rw [explicitCoeff0_baseUnitsEquivInvariants, toMul_ofMul, hv]
    exact congrArg (baseUnitsEquivInvariants K) (Additive.ofMul.apply_symm_apply c)

/-! ### The Kummer map on power classes -/

variable (K n)

/-! ### Surjectivity and the Kummer isomorphism -/

variable {K n}

variable (K n)

/-! ### Changing the level of the roots of unity

For `m ∣ n` with `n ≠ 0`, raising to the power `n / m` maps `μₙ` onto `μₘ` (at `n = 0` it is the
zero map, since `0 / m = 0`). On Kummer classes it is the change of level: an `n`th root `α` of
`a` gives the `m`th root `α ^ (n / m)` of the same `a`, and
`(g α / α) ^ (n / m) = g α ^ (n / m) / α ^ (n / m)`. When `n` is invertible in `K`, every class
at level `m` is a Kummer class, so the induced map on `H¹` is surjective
(`TauCeti.explicitCoeff1_kummerCoeffPow_surjective`). -/

variable {K n}

variable (K n)

/-! ### The Kummer map against canonical continuous cohomology -/

/-! ### Transport to another coefficient model -/

/-! ### Restriction along a field extension -/

section Restriction

variable (L : Type*) [Field L] [Algebra K L] (σ : L →ₐ[K] SeparableClosure K)

/-- The coefficient maps of restriction commute with the inclusion `μₙ ↪ (Kˢ)ˣ` of the Kummer
sequence. -/
@[simp]
theorem unitsCoeffMap_kummerCoeffIncl (x : KummerCoeff K n) :
    unitsCoeffMap K L σ (kummerCoeffIncl K n x) =
      kummerCoeffIncl L n (kummerCoeffMap K n L σ x) :=
  Additive.toMul.injective <| Units.ext <| by simp

variable {K n L} in
/-- **Transporting an `n`th root of a conjugate to `Lˢ`**: if `α ∈ Kˢ` is an `n`th root of `σ b`
for `b ∈ Lˣ`, its image under the inverse of the identification
`separableClosureRingEquiv K L σ : Lˢ ≃+* Kˢ` is an `n`th root of `b`. -/
theorem units_map_separableClosureRingEquiv_symm_pow_eq {b : Lˣ}
    (hα : (α : SeparableClosure K) ^ n = σ b) :
    Units.map (separableClosureRingEquiv K L σ).symm.toMonoidHom α ^ n =
      Units.map (algebraMap L (SeparableClosure L)).toMonoidHom b := by
  ext
  simp [← map_pow, hα]

end Restriction

/-! ### Pullback along an arbitrary field extension -/

section BaseChange

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]
variable (n : ℕ) (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

/-- **The Kummer isomorphism is natural for pullback along an arbitrary field extension**:
pullback along `τ : Kˢ → Lˢ` corresponds under the Kummer isomorphisms to the map of power classes
`Kˣ ⧸ (Kˣ)ⁿ → Lˣ ⧸ (Lˣ)ⁿ` induced by `K → L`. -/
theorem explicitMap1_kummerIso (hn : IsUnit (n : K)) (x : powerClassQuotient Kˣ n) :
    explicitMap1 (AbsoluteGaloisGroup K) (KummerCoeff K n) (AbsoluteGaloisGroup L)
      (KummerCoeff L n) (absoluteGaloisGroupMap τ) (kummerCoeffBaseChange n τ)
      continuous_of_discreteTopology (kummerCoeffBaseChange_smul n τ)
      (kummerIso K n hn x).toAdd =
        (kummerIso L n (by simpa using hn.map (algebraMap K L))
          (powerClassMap n (Units.map (algebraMap K L : K →* L)) x)).toAdd := by
  induction x using QuotientGroup.induction_on with
  | H a => rw [kummerIso_mk, powerClassMap_mk, kummerIso_mk, explicitMap1_kummerMap]

end BaseChange

/-! ### Corestriction along a finite extension, and the norm -/

section Corestriction

variable (L : Type*) [Field L] [Algebra K L] (σ : L →ₐ[K] SeparableClosure K)

variable [FiniteDimensional K L]

end Corestriction

end TauCeti
