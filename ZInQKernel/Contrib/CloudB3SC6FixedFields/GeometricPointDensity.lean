import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Algebraic-closure points detect morphisms

Extracted from the Anthropic Fermat's Last Theorem development, revision
`6e837e75355538c7f80bab5b956861e86c4eacc2`, file
`P2M/Sol/S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat.lean`,
helpers `RigKerGeomPoints` (lines 20–115).

Copyright 2026 Anthropic, PBC. Released under the Apache License, Version 2.0.
The source LICENSE, NOTICE and ATTRIBUTION.md are preserved alongside this module.

Changes: specialize the base domain to a field (so its generic fibre is the whole
scheme); isolate names; use selected Mathlib imports; replace the source's local
notation by `geometricBaseMap`; omit its Néron-carrier wrapper and port utilities.
`exists_geometric_point_mem` is a new consequence of the extracted density proof.
No curve, moduli, quotient, or function-field existence theorem is assumed.
-/

namespace CloudB3SC6FixedFields

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

universe u

noncomputable def geometricBaseMap (R L : Type u) [CommRing R] [Field L] [Algebra R L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R L))

section Density

variable {R L : Type u} [Field R] [Field L] [IsAlgClosed L] [Algebra R L]

/-- The algebraically closed field lies over the generic point of the domain. -/
theorem range_geometricBaseMap (hinj : Function.Injective (algebraMap R L)) :
    Set.range (geometricBaseMap R L).base = {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} := by
  ext p
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨q, rfl⟩
    rw [geometricBaseMap, Spec.map_base]
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R L) q.asIdeal = ⊥
    have hq : q.asIdeal = ⊥ := by
      haveI := q.isPrime
      exact Ideal.eq_bot_of_prime q.asIdeal
    rw [hq, Ideal.comap_bot_of_injective _ hinj]
  · rintro rfl
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    rw [geometricBaseMap, Spec.map_base]
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R L) ⊥ = ⊥
    exact Ideal.comap_bot_of_injective _ hinj

/-- Over a field the generic fibre is the entire scheme. -/
theorem dense_preimage_genericPoint {D : Scheme.{u}}
    (t : D ⟶ Spec (CommRingCat.of R)) [Flat t] :
    Dense (t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)}) := by
  intro p
  apply subset_closure
  change t.base p = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)
  exact Subsingleton.elim _ _

/-- Algebraically closed generic-fibre points are dense in a flat, locally finite-type scheme. -/
theorem dense_range_geometric_points (hinj : Function.Injective (algebraMap R L))
    {D : Scheme.{u}} (t : D ⟶ Spec (CommRingCat.of R)) [Flat t] [LocallyOfFiniteType t] :
    Dense (⋃ x : {x : Spec (CommRingCat.of L) ⟶ D // x ≫ t = geometricBaseMap R L},
      Set.range x.1.base) := by
  let P := pullback t (geometricBaseMap R L)
  haveI : LocallyOfFiniteType (pullback.snd t (geometricBaseMap R L)) := inferInstance
  haveI : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace (pullback.snd t (geometricBaseMap R L))
  have hsub : (pullback.fst t (geometricBaseMap R L)).base '' closedPoints P ⊆
      ⋃ x : {x : Spec (CommRingCat.of L) ⟶ D // x ≫ t = geometricBaseMap R L}, Set.range x.1.base := by
    rintro _ ⟨p, hp, rfl⟩
    let y := (pointEquivClosedPoint (pullback.snd t (geometricBaseMap R L))).symm ⟨p, hp⟩
    have hy : y.1 ≫ pullback.fst t (geometricBaseMap R L) ≫ t = geometricBaseMap R L := by
      rw [pullback.condition, ← Category.assoc, y.2, Category.id_comp]
    refine Set.mem_iUnion.mpr ⟨⟨y.1 ≫ pullback.fst t (geometricBaseMap R L), by
      rw [Category.assoc]; exact hy⟩, ⟨IsLocalRing.closedPoint L, ?_⟩⟩
    change (pullback.fst t (geometricBaseMap R L)).base (y.1.base (IsLocalRing.closedPoint L)) = _
    congr 1
    exact congrArg Subtype.val
      ((pointEquivClosedPoint (pullback.snd t (geometricBaseMap R L))).apply_symm_apply ⟨p, hp⟩)
  have hdenseP : Dense (closedPoints P) := by
    rw [dense_iff_closure_eq]
    have := JacobsonSpace.closure_inter_closedPoints_eq_closure (X := P) isOpen_univ.isLocallyClosed
    rw [Set.univ_inter, closure_univ] at this
    exact this
  have hrange : Set.range (pullback.fst t (geometricBaseMap R L)).base =
      t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} := by
    rw [Scheme.Pullback.range_fst, range_geometricBaseMap hinj]
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro d
  have h1 : d ∈ closure (t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)}) :=
    dense_preimage_genericPoint t d
  have h2 : t.base ⁻¹' {(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R)} ⊆
      closure ((pullback.fst t (geometricBaseMap R L)).base '' closedPoints P) := by
    rw [← hrange]
    rintro _ ⟨p, rfl⟩
    have : p ∈ closure (closedPoints P) := hdenseP p
    exact map_mem_closure (pullback.fst t (geometricBaseMap R L)).base.hom.continuous this
      (fun q hq => ⟨q, hq, rfl⟩)
  have h3 := closure_mono h2
  rw [closure_closure] at h3
  exact closure_mono hsub (h3 h1)

/-- Every nonempty open contains an algebraically closed generic-fibre point. -/
theorem exists_geometric_point_mem (hinj : Function.Injective (algebraMap R L))
    {D : Scheme.{u}} (t : D ⟶ Spec (CommRingCat.of R)) [Flat t] [LocallyOfFiniteType t]
    (U : D.Opens) (hU : (U : Set D).Nonempty) :
    ∃ y : Spec (CommRingCat.of L) ⟶ D,
      y ≫ t = geometricBaseMap R L ∧ (Scheme.SpecToEquivOfField L D y).1 ∈ U := by
  obtain ⟨d, hd⟩ := hU
  obtain ⟨p, hpU, hp⟩ := (mem_closure_iff.mp (dense_range_geometric_points hinj t d))
    (U : Set D) U.isOpen hd
  obtain ⟨y, z, rfl⟩ := Set.mem_iUnion.mp hp
  refine ⟨y.1, y.2, ?_⟩
  change y.1 (IsLocalRing.closedPoint L) ∈ (U : Set D)
  change y.1 z ∈ (U : Set D) at hpU
  rw [Subsingleton.elim z (IsLocalRing.closedPoint L)] at hpU
  exact hpU

/-- Morphisms to a separated target are determined by algebraic-closure points. -/
theorem hom_ext_of_geometric_points (hinj : Function.Injective (algebraMap R L))
    {Y X : Scheme.{u}} (t : Y ⟶ Spec (CommRingCat.of R)) (s : X ⟶ Spec (CommRingCat.of R))
    [Flat t] [LocallyOfFiniteType t] [IsSeparated s] [IsReduced Y]
    (φ ψ : Y ⟶ X) (hφ : φ ≫ s = t) (hψ : ψ ≫ s = t)
    (h : ∀ x : Spec (CommRingCat.of L) ⟶ Y,
      x ≫ t = geometricBaseMap R L → x ≫ φ = x ≫ ψ) : φ = ψ := by
  let I := {x : Spec (CommRingCat.of L) ⟶ Y // x ≫ t = geometricBaseMap R L}
  let W : Scheme.{u} := ∐ fun _ : I => Spec (CommRingCat.of L)
  let ι : W ⟶ Y := Sigma.desc fun x : I => x.1
  haveI : IsDominant ι := by
    rw [isDominant_iff]
    have hd := dense_range_geometric_points hinj t
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

end Density

end CloudB3SC6FixedFields
