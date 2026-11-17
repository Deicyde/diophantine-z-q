/-
# H5 / NOS round 2, lane 1: the single-arbitrary-order specialization injection

Derived from `theorem solution` (lines 392–509) of
`P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_isTorsionPoint_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self.lean`
in `anthropics/fermats-last-theorem` at revision `6e837e75355538c7f80bab5b956861e86c4eacc2`
(Git blob `101b54b0bb570c47a4c2ad04775dfabdf5396b49`, 59,913 bytes).
Copyright 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0; see the
`LICENSE`/`NOTICE` files shipped with this contribution (verbatim copies of the source's).

NOTICE OF MODIFICATION (Apache-2.0 §4(b)), 2026-11-14 (H5 round-2 lane 1):
* The prime-power data `(ℓ, hℓu : IsUnit (ℓ : R), v)` of the source theorem is replaced by ONE
  arbitrary order `m` with `hmR : IsUnit (m : R)`; no primality, tower or divisibility closure.
* The source's inertia hypothesis quantified over every power `ℓ ^ v`; here it is required at the
  single order `m` only. In the source body it is used exactly once, at the already chosen
  order (source line 468, `hunr A hRA σ hσ v _ hx`); here `hunr A hRA σ hσ _ hx`.
* The conclusion indexes by `Fin (m ^ (2 * d))` instead of `Fin (ℓ ^ (2 * d * v))`; the
  source's final `pow_mul` re-indexing (source lines 501–507) is no longer needed.
* The source fixes the geometric point field to `AlgebraicClosure K`. The main theorem here
  takes an ARBITRARY algebraic closure `Ω` (`[Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]`), so a
  model over an intermediate base `K = E ⊆ Ω₀` can use the original closure `Ω₀`. The inertia
  hypothesis is stated for valuation subrings `A` of `Ω` with `algebraMap K Ω (algebraMap R K r) ∈ A`
  for all `r : R` (no `Algebra R Ω` instance is assumed; the proof uses the composite one).
  The helpers this relies on take an arbitrary `Ω` in the source itself:
  `P2mSerreTateLemmaTwo.finite_and_natCard_torsion` (`[IsAlgClosed Ω]`, source lines 93–99),
  `exists_isGalois_forall_isTorsionPoint_exists_specMap_comp_eq_and_forall_eq_one` (`[Normal K Ω]`)
  and `ValuationSubring.exists_mem_inertiaSubgroupIn_and_forall_apply_algebraMap_eq`
  (`[Normal K Ω]`, any tower `K → L → Ω`). The source-shaped statement with
  `AlgebraicClosure K` is kept as a wrapper (`…_of_singleOrder`).
* Every other step is the source proof verbatim. The source's helper section
  `P2mSerreTateLemmaTwo` (count transport, integral closure, inertia comparison,
  unramifiedness, residue point) is NOT restated: it is imported from the lane-4 port of the
  original module (declaration prefix `ZInQ.Contrib.CloudW03NeronSurj.FLT`, as for H76).
* The supplied Néron model `hN : NeronModelPropertyBundle R K g` stays an explicit argument:
  this is an intermediate interface, not a closure of `PkgI2.NeronOggShafarevich`.
A source-layout version of the order change and its unified diff against the original module
are kept in the lane-1 report directory (`source-refactor/`, `logs/injection-singleOrder.diff`).
-/
import ZInQKernel.Contrib.CloudR2NOS.Source.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_isTorsionPoint_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

w03_open "AlgebraicGeometry"

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_isTorsionPoint_of_neronModelPropertyBundle_of_singleOrder

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped Pointwise

universe u

open P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_isTorsionPoint_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self.P2mSerreTateLemmaTwo in

/-- Single-order specialization injection, for an arbitrary algebraic closure `Ω` of `K`:
for ONE order `m` invertible in the DVR `R`, if the inertia groups (over `K`) of all valuation
subrings of `Ω` containing (the image of) `R` fix the geometric generic-fibre `m`-torsion, then
`Fin (m ^ (2 * d))` injects into the `m`-torsion of the supplied Néron model at a geometric point
of the special fibre. -/
theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (hBK : AbelianSchemePropertyBundle K (pullback.snd g (specGenericFibreInclusion R K)))
    (d : ℕ) [SmoothOfRelativeDimension d (pullback.snd g (specGenericFibreInclusion R K))]
    (m : ℕ) (hmR : IsUnit (m : R))
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (hunr : ∀ (A : ValuationSubring Ω),
      (∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) →
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ A.inertiaSubgroupIn K →
      ∀ (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
          (pullback.snd g (specGenericFibreInclusion R K))),
        (LB.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) m x →
          Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.1 = x.1)
    (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra R k']
    (hk' : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R k' r = 0) :
    ∃ r : Fin (m ^ (2 * d)) →
        {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
          LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) m y},
      Function.Injective r := by
  classical
  -- The composite `R → K → Ω`; only used internally (to form `integralClosure R L`).
  letI : Algebra R Ω := ((algebraMap K Ω).comp (algebraMap R K)).toAlgebra
  haveI : IsScalarTower R K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

  have hnR : IsUnit ((m : ℕ) : R) := hmR
  have hnK : ((m : ℕ) : K) ≠ 0 := by
    have h := hnR.map (algebraMap R K)
    rw [map_natCast] at h
    exact h.ne_zero
  have hcK : (LB.genericFibre K).IsCommutative :=
    RelativeGroupLaw.IsCommutative.baseChange _ (fun t x y => hcomm t x y)

  obtain ⟨hfin, hcard⟩ := finite_and_natCard_torsion (LB.genericFibre K) hcK hBK d m hnK Ω

  obtain ⟨L, hfd, hgal, hdesc, hfaith⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isGalois_forall_isTorsionPoint_exists_specMap_comp_eq_and_forall_eq_one
      K (LB.genericFibre K) (fun t x y => hcK t x y) hBK d m hnK Ω
  haveI := hfd
  haveI := hgal

  haveI := isFractionRing_integralClosure K L (R := R)
  haveI := isDedekindDomain_integralClosure K L (R := R)
  haveI := module_finite_integralClosure K L (R := R)

  obtain ⟨P, hPmax, hPover, ψ, hψ⟩ := exists_ideal_algHom_of_isAlgClosed
    (S := integralClosure R L) k' hk' (RingHom.ker_ne_top _)
  have hP0 : P ≠ ⊥ := ne_bot_of_liesOver_maximalIdeal (K := K) P

  have hinert : P.inertia (L ≃ₐ[K] L) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun τ hτ => hfaith τ fun z hz => ?_
    let vP : IsDedekindDomain.HeightOneSpectrum (integralClosure R L) := ⟨P, hPmax.isPrime, hP0⟩
    haveI : vP.asIdeal.IsMaximal := hPmax
    have hτv := mem_inertiaSubgroupIn_of_mem_inertia vP τ hτ
    obtain ⟨A, σ, hA, hσ, hστ⟩ :=
      ValuationSubring.exists_mem_inertiaSubgroupIn_and_forall_apply_algebraMap_eq K
        (Ω := Ω) _ τ hτv

    have hRA : ∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A := by
      intro r
      have h1 : algebraMap K Ω (algebraMap R K r) =
          algebraMap L Ω (algebraMap R L r) := by
        rw [IsScalarTower.algebraMap_apply R K L, ← IsScalarTower.algebraMap_apply K L Ω]
      rw [h1, ← ValuationSubring.mem_comap, hA,
        IsScalarTower.algebraMap_apply R (integralClosure R L) L]
      exact algebraMap_mem_valuationSubringAtPrime vP _

    have hcomp : Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) =
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    have hx := (LB.genericFibre K).isTorsionPoint_schemeHomOverComp _ _ _ hcomp m hz
    -- The only use of the inertia hypothesis: at the single chosen order `m`.
    have hfix := hunr A hRA σ hσ _ hx
    rw [GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp] at hfix
    have hring : (σ : Ω →+* Ω).comp (algebraMap L Ω) =
        (algebraMap L Ω).comp (τ : L →+* L) :=
      RingHom.ext fun x => by simpa using hστ x
    rw [hring, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] at hfix
    haveI := epi_specMap_of_field (algebraMap L Ω)
    exact (cancel_epi _).mp hfix
  haveI : Algebra.IsUnramifiedAt R P := isUnramifiedAt_of_inertia_eq_bot (K := K) P hinert

  haveI : P.IsPrime := hPmax.isPrime
  obtain ⟨r₁, hr₁⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_injective_specialize_isTorsionPoint_of_isUnramifiedAt
      K LB hcomm hN m hnR (integralClosure R L) L P k' ψ hψ

  let δ : {x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
        (pullback.snd g (specGenericFibreInclusion R K)) //
      (LB.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) m x} →
      {z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L)))
        (pullback.snd g (specGenericFibreInclusion R K)) //
      (LB.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L)))
        m z} :=
    fun x => ⟨(hdesc x.1 x.2).choose, (hdesc x.1 x.2).choose_spec.1⟩
  have hδ : Function.Injective δ := by
    intro x x' h
    apply Subtype.ext
    apply Subtype.ext
    rw [← (hdesc x.1 x.2).choose_spec.2, ← (hdesc x'.1 x'.2).choose_spec.2]
    exact congrArg (fun z => Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ z.1.1) h
  haveI := hfin
  let e := Finite.equivFinOfCardEq hcard
  exact ⟨fun i => r₁ (δ (e.symm i)), hr₁.comp (hδ.comp e.symm.injective)⟩

end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_isTorsionPoint_of_neronModelPropertyBundle_of_singleOrder

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

/-- Statement-level export of the single-order injection for an ARBITRARY algebraic closure `Ω`
of `K` (new name; distinct suffix, no clash with any source declaration). Intermediate
interface: the Néron model `hN` is explicit. -/
theorem GoodReductionJacobian.RelativeGroupLaw.exists_injective_isTorsionPoint_of_neronModelPropertyBundle_of_singleOrder_isAlgClosure
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (hBK : AbelianSchemePropertyBundle K (pullback.snd g (specGenericFibreInclusion R K)))
    (d : ℕ) [SmoothOfRelativeDimension d (pullback.snd g (specGenericFibreInclusion R K))]
    (m : ℕ) (hmR : IsUnit (m : R))
    (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (hunr : ∀ (A : ValuationSubring Ω),
      (∀ r : R, algebraMap K Ω (algebraMap R K r) ∈ A) →
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ A.inertiaSubgroupIn K →
      ∀ (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
          (pullback.snd g (specGenericFibreInclusion R K))),
        (LB.genericFibre K).IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) m x →
          Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) ≫ x.1 = x.1)
    (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra R k']
    (hk' : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R k' r = 0) :
    ∃ r : Fin (m ^ (2 * d)) →
        {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
          LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) m y},
      Function.Injective r :=
  P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_injective_isTorsionPoint_of_neronModelPropertyBundle_of_singleOrder.solution
    K LB hcomm hN hBK d m hmR Ω hunr k' hk'

/-- The source-shaped wrapper, with the source's fixed closure `AlgebraicClosure K` and the
source's form `algebraMap R (AlgebraicClosure K) r ∈ A` of the containment condition. -/
theorem GoodReductionJacobian.RelativeGroupLaw.exists_injective_isTorsionPoint_of_neronModelPropertyBundle_of_singleOrder
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {B : Scheme.{u}} {g : B ⟶ Spec (CommRingCat.of R)} (LB : RelativeGroupLaw R g)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t g),
      LB.mul t x y = LB.mul t y x)
    (hN : NeronModelPropertyBundle R K g)
    (hBK : AbelianSchemePropertyBundle K (pullback.snd g (specGenericFibreInclusion R K)))
    (d : ℕ) [SmoothOfRelativeDimension d (pullback.snd g (specGenericFibreInclusion R K))]
    (m : ℕ) (hmR : IsUnit (m : R))
    (hunr : ∀ (A : ValuationSubring (AlgebraicClosure K)),
      (∀ r : R, algebraMap R (AlgebraicClosure K) r ∈ A) →
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, σ ∈ A.inertiaSubgroupIn K →
      ∀ (x : SchemeHomOver
          (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
          (pullback.snd g (specGenericFibreInclusion R K))),
        (LB.genericFibre K).IsTorsionPoint
            (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))) m x →
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure K →+* AlgebraicClosure K)) ≫ x.1 =
            x.1)
    (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra R k']
    (hk' : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R k' r = 0) :
    ∃ r : Fin (m ^ (2 * d)) →
        {y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R k'))) g //
          LB.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap R k'))) m y},
      Function.Injective r :=
  GoodReductionJacobian.RelativeGroupLaw.exists_injective_isTorsionPoint_of_neronModelPropertyBundle_of_singleOrder_isAlgClosure
    K LB hcomm hN hBK d m hmR (AlgebraicClosure K)
    (fun A hA => hunr A (fun r => by
      rw [IsScalarTower.algebraMap_apply R K (AlgebraicClosure K)]
      exact hA r))
    k' hk'

end ZInQ.Contrib.CloudW03NeronSurj.FLT
