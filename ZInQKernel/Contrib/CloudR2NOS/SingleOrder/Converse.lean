/-
# H5 / NOS round 2, lane 1: the infinite-orders source converse (supplied Néron model)

Derived from `theorem solution` of
`P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self.lean`
in `anthropics/fermats-last-theorem` at revision `6e837e75355538c7f80bab5b956861e86c4eacc2`
(Git blob `f6e62ee59f8f99f9407e908e7ae01fc6ca185d09`, 44,363 bytes).
Copyright 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0; see the
`LICENSE`/`NOTICE` files shipped with this contribution (verbatim copies of the source's).

NOTICE OF MODIFICATION (Apache-2.0 §4(b)), 2026-11-14 (H5 round-2 lane 1):
* The source assumes ONE invertible prime `ℓ` and inertia-triviality on ALL powers `ℓ ^ v`, and
  derives the contradiction at the order `ℓ ^ c` via `key_ineq`. Here the hypothesis is an
  arbitrary INFINITE set `S` of orders invertible in `R`, each satisfying the inertia condition at
  that single order only. No prime recurs, no divisibility closure of `S` and no tower is used.
* In the nonproper branch of the special-fibre alternative
  `forall_isProper_or_exists_natCard_isTorsionPoint_le_mul_pow` (one constant `c` for ALL orders
  `m` with `(m : k) ≠ 0`: quantifier order `∃ c, ∀ m`), ONE order `m ∈ S` with `m > c` is chosen
  (`Set.Infinite.exists_gt`); its residue is nonzero because `m` is a unit of `R`.
* The single-order injection (`Injection.lean`) gives `m ^ (2 * d) ≤ #B(k̄)[m]`, the uniform bound
  gives `#B(k̄)[m] ≤ c * m ^ (2 * d - 1)`, and `Arith.lean` gives `c * m ^ (2 * d - 1) < m ^ (2 * d)`.
* The geometric generic point field is an ARBITRARY algebraic closure `Ω` of `K`
  (`[IsAlgClosure K Ω]`), not only `AlgebraicClosure K`; the containment condition is
  `algebraMap K Ω (algebraMap R K r) ∈ A`. The source-shaped statements with `AlgebraicClosure K`
  are kept as wrappers. The special-fibre point field stays the source's `AlgebraicClosure k`.
* The proper branch is the source's verbatim: properness of the identity component and the
  source theorem `abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_forall_isProper`.
* The source's helper section `P2mNOSConverseAssembly` (torsion transport along base change) is
  imported from the lane-4 port of the original module, not restated.
* The supplied Néron model `hN` stays an explicit argument: an intermediate interface, not a
  closure of `PkgI2.NeronOggShafarevich`.
A source-layout version of the order change and its unified diff against the original module
are kept in the lane-1 report directory (`source-refactor/`, `logs/converse-infiniteOrders.diff`).
-/
import ZInQKernel.Contrib.CloudR2NOS.Source.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self
import ZInQKernel.Contrib.CloudR2NOS.SingleOrder.Injection
import ZInQKernel.Contrib.CloudR2NOS.SingleOrder.Arith
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

w03_open "AlgebraicGeometry"

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_infinite_singleOrder

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

open P2MW.S_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self.P2mNOSConverseAssembly in

/-- Infinite-orders converse for a SUPPLIED Néron model and an arbitrary algebraic closure `Ω`
of `K`: if an infinite set `S` of orders invertible in the DVR `R` satisfies, for each `m ∈ S`
separately, inertia-triviality on the geometric generic-fibre `m`-torsion over `Ω`, then the Néron
model is an abelian scheme. -/
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (hBK : AbelianSchemePropertyBundle K (pullback.snd g (specGenericFibreInclusion R K)))
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (S : Set ℕ) (hS : S.Infinite) (hSu : ∀ m ∈ S, IsUnit (m : R))
    (hunr : ∀ m ∈ S, ∀ (A : ValuationSubring Ω),
      (∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) →
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ A.inertiaSubgroupIn K →
      ∀ (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
          (pullback.snd g (specGenericFibreInclusion R K))),
        (LB.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) m x →
          Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.1 = x.1) :
    AbelianSchemePropertyBundle R g := by
  classical

  haveI : Smooth g := hN.smooth
  haveI : IsSeparated g := hN.separated
  haveI : LocallyOfFiniteType g := hN.locallyOfFiniteType
  haveI : QuasiCompact g := hN.quasiCompact
  obtain ⟨d, hd⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing LB
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := d)
  haveI : SmoothOfRelativeDimension d (pullback.snd g (specGenericFibreInclusion R K)) :=
    MorphismProperty.pullback_snd _ _ hd

  set k : Type u := IsLocalRing.ResidueField R with hk
  set ι : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)) with hι
  haveI : SmoothOfRelativeDimension d (pullback.snd g ι) := MorphismProperty.pullback_snd _ _ hd
  have hc : (LB.baseChange ι).IsCommutative :=
    RelativeGroupLaw.IsCommutative.baseChange ι (fun t x y => hcomm t x y)
  set k' : Type u := AlgebraicClosure k with hk'

  rcases GoodReductionJacobian.RelativeGroupLaw.forall_isProper_or_exists_natCard_isTorsionPoint_le_mul_pow
      k (pullback.snd g ι) (LB.baseChange ι) hc d k' with hprop | ⟨hdpos, c, hbound⟩
  · exact GoodReductionJacobian.RelativeGroupLaw.abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_forall_isProper
      K LB hN hBK hprop
  · exfalso
    have hk'zero : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R k' r = 0 := by
      intro r hr
      rw [IsScalarTower.algebraMap_apply R k k', IsLocalRing.ResidueField.algebraMap_eq,
        (IsLocalRing.residue_eq_zero_iff r).mpr hr, map_zero]
    -- ONE order of `S` above the uniform constant `c` (replaces the source's choice `ℓ ^ c`).
    obtain ⟨m, hmS, hcm⟩ := hS.exists_gt c
    have hmR : IsUnit (m : R) := hSu m hmS
    obtain ⟨r, hr⟩ :=
      GoodReductionJacobian.RelativeGroupLaw.exists_injective_isTorsionPoint_of_neronModelPropertyBundle_of_singleOrder_isAlgClosure
        K LB hcomm hN hBK d m hmR Ω (hunr m hmS) k' hk'zero

    have hm : (m : k) ≠ 0 := by
      have hu := hmR.map (algebraMap R k)
      rw [map_natCast] at hu
      exact hu.ne_zero
    obtain ⟨hfin, hcard⟩ := hbound m hm

    set t' : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k k')) with ht'
    have hcomp : t' ≫ ι = Spec.map (CommRingCat.ofHom (algebraMap R k')) := by
      rw [ht', hι, ← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq R k k',
        IsLocalRing.ResidueField.algebraMap_eq]
    let e := (torsionEquivBaseChange ι LB t' m).trans (torsionEquivOfEq LB hcomp m)
    haveI : Finite {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
        LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) m y} :=
      Finite.of_equiv _ e
    have h2 : Nat.card {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
        LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) m y} ≤
        c * m ^ (2 * d - 1) := by
      rw [← Nat.card_congr e]; exact hcard
    exact _root_.ZInQ.Contrib.CloudR2NOS.SingleOrder.false_of_injective_of_natCard_le
      hdpos hcm hr h2

end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_infinite_singleOrder

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

/-- Statement-level export of the infinite-orders converse for an ARBITRARY algebraic closure `Ω`
of `K` (new name, distinct suffix). Intermediate interface: the Néron model `hN` is supplied. -/
theorem GoodReductionJacobian.RelativeGroupLaw.abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_infinite_singleOrder_isAlgClosure
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (hBK : AbelianSchemePropertyBundle K (pullback.snd g (specGenericFibreInclusion R K)))
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (S : Set ℕ) (hS : S.Infinite) (hSu : ∀ m ∈ S, IsUnit (m : R))
    (hunr : ∀ m ∈ S, ∀ (A : ValuationSubring Ω),
      (∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) →
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ A.inertiaSubgroupIn K →
      ∀ (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
          (pullback.snd g (specGenericFibreInclusion R K))),
        (LB.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) m x →
          Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.1 = x.1) :
    AbelianSchemePropertyBundle R g :=
  P2MW.S_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_infinite_singleOrder.solution
    K LB hcomm hN hBK Ω S hS hSu hunr

/-- The same converse (arbitrary `Ω`) with the orders given in the exact shape of the original
target's set, `{m : ℕ | 0 < m ∧ IsUnit (m : R) ∧ Q m}`, where `Q m` is any order predicate
implying the single-order inertia condition at `m`. -/
theorem GoodReductionJacobian.RelativeGroupLaw.abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_infinite_setOf_singleOrder_isAlgClosure
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (hBK : AbelianSchemePropertyBundle K (pullback.snd g (specGenericFibreInclusion R K)))
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Q : ℕ → Prop) (hS : {m : ℕ | 0 < m ∧ IsUnit (m : R) ∧ Q m}.Infinite)
    (hunr : ∀ m : ℕ, 0 < m → IsUnit (m : R) → Q m →
      ∀ (A : ValuationSubring Ω),
      (∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) →
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ A.inertiaSubgroupIn K →
      ∀ (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
          (pullback.snd g (specGenericFibreInclusion R K))),
        (LB.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) m x →
          Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.1 = x.1) :
    AbelianSchemePropertyBundle R g :=
  GoodReductionJacobian.RelativeGroupLaw.abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_infinite_singleOrder_isAlgClosure
    K LB hcomm hN hBK Ω _ hS (fun _ hm => hm.2.1) (fun m hm => hunr m hm.1 hm.2.1 hm.2.2)

/-- Source-shaped wrapper: the source's fixed closure `AlgebraicClosure K` and its containment
form `algebraMap R (AlgebraicClosure K) r ∈ A`. -/
theorem GoodReductionJacobian.RelativeGroupLaw.abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_infinite_singleOrder
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (hBK : AbelianSchemePropertyBundle K (pullback.snd g (specGenericFibreInclusion R K)))
    (S : Set ℕ) (hS : S.Infinite) (hSu : ∀ m ∈ S, IsUnit (m : R))
    (hunr : ∀ m ∈ S, ∀ (A : ValuationSubring (AlgebraicClosure K)),
      (∀ r : R, algebraMap R (AlgebraicClosure K) r ∈ A) →
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, σ ∈ A.inertiaSubgroupIn K →
      ∀ (x : SchemeHomOver
          (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
          (pullback.snd g (specGenericFibreInclusion R K))),
        (LB.genericFibre K).IsTorsionPoint
            (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) m x →
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ x.1 =
            x.1) :
    AbelianSchemePropertyBundle R g :=
  GoodReductionJacobian.RelativeGroupLaw.abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_infinite_singleOrder_isAlgClosure
    K LB hcomm hN hBK (AlgebraicClosure K) S hS hSu
    (fun m hmS A hA => hunr m hmS A (fun r => by
      rw [IsScalarTower.algebraMap_apply R K (AlgebraicClosure K)]
      exact hA r))

/-- Source-shaped wrapper of the target-set-shaped converse (`AlgebraicClosure K`). -/
theorem GoodReductionJacobian.RelativeGroupLaw.abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_infinite_setOf_singleOrder
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (hBK : AbelianSchemePropertyBundle K (pullback.snd g (specGenericFibreInclusion R K)))
    (Q : ℕ → Prop) (hS : {m : ℕ | 0 < m ∧ IsUnit (m : R) ∧ Q m}.Infinite)
    (hunr : ∀ m : ℕ, 0 < m → IsUnit (m : R) → Q m →
      ∀ (A : ValuationSubring (AlgebraicClosure K)),
      (∀ r : R, algebraMap R (AlgebraicClosure K) r ∈ A) →
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, σ ∈ A.inertiaSubgroupIn K →
      ∀ (x : SchemeHomOver
          (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
          (pullback.snd g (specGenericFibreInclusion R K))),
        (LB.genericFibre K).IsTorsionPoint
            (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) m x →
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ x.1 =
            x.1) :
    AbelianSchemePropertyBundle R g :=
  GoodReductionJacobian.RelativeGroupLaw.abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_infinite_singleOrder
    K LB hcomm hN hBK _ hS (fun _ hm => hm.2.1) (fun m hm => hunr m hm.1 hm.2.1 hm.2.2)

end ZInQ.Contrib.CloudW03NeronSurj.FLT
