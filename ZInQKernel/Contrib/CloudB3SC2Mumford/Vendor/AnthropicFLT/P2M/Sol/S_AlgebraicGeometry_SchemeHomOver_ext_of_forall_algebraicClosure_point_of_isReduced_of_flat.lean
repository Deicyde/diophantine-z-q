/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

open Topology CategoryTheory.Limits

namespace RigKerGeomPoints

variable {R L : Type u} [CommRing R] [IsDomain R] [Field L] [IsAlgClosed L] [Algebra R L]

-- [port] local notation `bL` removed (build-time syntax); its uses below are expanded to `(Spec.map (CommRingCat.ofHom (algebraMap R L)))`

theorem range_specMap_eq (hinj : Function.Injective (algebraMap R L)) :
    -- [port] Mathlib v4.35: `Ideal.bot_prime` is `Ideal.isPrime_bot`
    Set.range ((Spec.map (CommRingCat.ofHom (algebraMap R L)))).base = {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} := by
  ext p
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨q, rfl⟩
    rw [Spec.map_base]
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R L) q.asIdeal = ⊥
    have hq : q.asIdeal = ⊥ := by
      haveI := q.isPrime
      exact Ideal.eq_bot_of_prime q.asIdeal
    rw [hq, Ideal.comap_bot_of_injective _ hinj]
  · rintro rfl
    -- [port] Mathlib v4.35: `Ideal.bot_prime` is `Ideal.isPrime_bot`
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    rw [Spec.map_base]
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R L) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ hinj

omit [IsAlgClosed L] [Algebra R L] in

theorem dense_preimage_genericPoint {D : Scheme.{u}} (t : D ⟶ Spec (CommRingCat.of R)) [Flat t] :
    -- [port] Mathlib v4.35: `Ideal.bot_prime` is `Ideal.isPrime_bot`
    Dense (t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)}) := by
  intro p
  -- [port] Mathlib v4.35: `Ideal.bot_prime` is `Ideal.isPrime_bot`
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ⤳ t.base p := by
    rw [← PrimeSpectrum.le_iff_specializes]
    exact bot_le
  obtain ⟨q, hq, htq⟩ := Flat.generalizingMap t hgen
  -- [port] Mathlib v4.35: `Ideal.bot_prime` is `Ideal.isPrime_bot`
  have hqmem : q ∈ t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} := htq
  apply closure_mono (Set.singleton_subset_iff.mpr hqmem)
  exact hq.mem_closure

theorem dense_range_of_points (hinj : Function.Injective (algebraMap R L))
    {D : Scheme.{u}} (t : D ⟶ Spec (CommRingCat.of R)) [Flat t] [LocallyOfFiniteType t] :
    Dense (⋃ x : {x : Spec (CommRingCat.of L) ⟶ D // x ≫ t = (Spec.map (CommRingCat.ofHom (algebraMap R L)))},
      Set.range x.1.base) := by
  let P := pullback t (Spec.map (CommRingCat.ofHom (algebraMap R L)))
  haveI : LocallyOfFiniteType (pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap R L)))) := inferInstance
  haveI : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace (pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap R L))))
  have hsub : (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap R L)))).base '' closedPoints P ⊆
      ⋃ x : {x : Spec (CommRingCat.of L) ⟶ D // x ≫ t = (Spec.map (CommRingCat.ofHom (algebraMap R L)))}, Set.range x.1.base := by
    rintro _ ⟨p, hp, rfl⟩
    let y := (pointEquivClosedPoint (pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap R L))))).symm ⟨p, hp⟩
    have hy : y.1 ≫ pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap R L))) ≫ t = (Spec.map (CommRingCat.ofHom (algebraMap R L))) := by
      rw [pullback.condition, ← Category.assoc, y.2, Category.id_comp]
    refine Set.mem_iUnion.mpr ⟨⟨y.1 ≫ pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap R L))), by rw [Category.assoc]; exact hy⟩,
      ⟨IsLocalRing.closedPoint L, ?_⟩⟩
    change (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap R L)))).base (y.1.base (IsLocalRing.closedPoint L)) = _
    congr 1
    have := pointEquivClosedPoint_symm_apply_coe (pullback.snd t (Spec.map (CommRingCat.ofHom (algebraMap R L)))) ⟨p, hp⟩
    change y.1 = _ at this
    rw [this, pointOfClosedPoint_apply]
  have hdenseP : Dense (closedPoints P) := by
    rw [dense_iff_closure_eq]
    have := JacobsonSpace.closure_inter_closedPoints_eq_closure (X := P) isOpen_univ.isLocallyClosed
    rw [Set.univ_inter, closure_univ] at this
    exact this
  -- [port] Mathlib v4.35: `Ideal.bot_prime` is `Ideal.isPrime_bot`
  have hrange : Set.range (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap R L)))).base = t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} := by
    rw [Scheme.Pullback.range_fst, range_specMap_eq hinj]
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro d
  -- [port] Mathlib v4.35: `Ideal.bot_prime` is `Ideal.isPrime_bot`
  have h1 : d ∈ closure (t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)}) :=
    dense_preimage_genericPoint t d
  -- [port] Mathlib v4.35: `Ideal.bot_prime` is `Ideal.isPrime_bot`
  have h2 : t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} ⊆
      closure ((pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap R L)))).base '' closedPoints P) := by
    rw [← hrange]
    rintro _ ⟨p, rfl⟩
    have : p ∈ closure (closedPoints P) := hdenseP p
    exact (map_mem_closure (pullback.fst t (Spec.map (CommRingCat.ofHom (algebraMap R L)))).base.hom.continuous this fun q hq => ⟨q, hq, rfl⟩)
  have h3 := closure_mono h2
  rw [closure_closure] at h3
  exact closure_mono hsub (h3 h1)

theorem ext_of_forall_geometric_point (hinj : Function.Injective (algebraMap R L))
    {Y X : Scheme.{u}} (t : Y ⟶ Spec (CommRingCat.of R)) (s : X ⟶ Spec (CommRingCat.of R))
    [Flat t] [LocallyOfFiniteType t] [IsSeparated s] [IsReduced Y]
    (φ ψ : Y ⟶ X) (hφ : φ ≫ s = t) (hψ : ψ ≫ s = t)
    (h : ∀ x : Spec (CommRingCat.of L) ⟶ Y, x ≫ t = (Spec.map (CommRingCat.ofHom (algebraMap R L))) → x ≫ φ = x ≫ ψ) : φ = ψ := by
  let I := {x : Spec (CommRingCat.of L) ⟶ Y // x ≫ t = (Spec.map (CommRingCat.ofHom (algebraMap R L)))}
  let W : Scheme.{u} := ∐ fun _ : I => Spec (CommRingCat.of L)
  let ι : W ⟶ Y := Sigma.desc fun x : I => x.1
  haveI : IsDominant ι := by
    rw [isDominant_iff]
    have hd := dense_range_of_points (L := L) hinj t
    refine Dense.mono ?_ hd
    intro d hd'
    obtain ⟨x, ⟨p, rfl⟩⟩ := Set.mem_iUnion.mp hd'
    refine ⟨(Sigma.ι (fun _ : I => Spec (CommRingCat.of L)) x).base p, ?_⟩
    change (Sigma.ι (fun _ : I => Spec (CommRingCat.of L)) x ≫ ι).base p = _
    rw [Sigma.ι_desc]
  refine ext_of_isDominant_of_isSeparated s (hφ.trans hψ.symm) ι ?_
  apply Sigma.hom_ext
  intro x
  rw [← Category.assoc, ← Category.assoc, Sigma.ι_desc]
  exact h x.1 x.2

end RigKerGeomPoints

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (Kbar : Type u) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar] [Algebra R Kbar] [IsScalarTower R K Kbar]
    {Y X : Scheme.{u}} {gY : Y ⟶ Spec (CommRingCat.of R)} {gX : X ⟶ Spec (CommRingCat.of R)}
    [Flat gY] [LocallyOfFiniteType gY] [IsReduced Y] [IsSeparated gX]
    (φ ψ : SchemeHomOver gY gX)
    (h : ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) gY, x.1 ≫ φ.1 = x.1 ≫ ψ.1) :
    φ = ψ := by
  haveI : IsAlgClosed Kbar := IsAlgClosure.isAlgClosed K
  have hinj : Function.Injective (algebraMap R Kbar) := by
    rw [IsScalarTower.algebraMap_eq R K Kbar]
    exact (algebraMap K Kbar).injective.comp (IsFractionRing.injective R K)
  apply Subtype.ext
  exact RigKerGeomPoints.ext_of_forall_geometric_point (L := Kbar) hinj gY gX φ.1 ψ.1 φ.2 ψ.2
    (fun x hx => h ⟨x, hx⟩)
