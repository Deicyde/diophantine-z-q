import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_Algebra_FiniteType_exists_notMem_under_forall_trdeg_quotient_le.lean
Original Git blob: 4612889e5d2c53741a5a2179e16cc20843c1c251
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_Algebra_exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "Polynomial"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_Algebra_FiniteType_exists_notMem_under_forall_trdeg_quotient_le
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

universe u v

namespace P2mGenericTrdegBound
h77_bridge_namespace

theorem isIntegral_map_of_forall_mem {R R' C C' : Type*} [CommRing R] [CommRing R'] [CommRing C] [CommRing C']
    [Algebra R C] [Algebra R' C'] (f : C →+* C') (D : Subalgebra R C) (D' : Subalgebra R' C')
    (hDD' : ∀ x ∈ D, f x ∈ D') {x : C} (hx : IsIntegral D x) : IsIntegral D' (f x) := by
  obtain ⟨p, hmonic, hp⟩ := hx
  let φ : D →+* D' := (f.comp (algebraMap D C)).codRestrict D'.toSubring
    (fun d => hDD' _ (by exact d.2))
  have hφ : (algebraMap D' C').comp φ = f.comp (algebraMap D C) := by
    ext d; rfl
  refine ⟨p.map φ, hmonic.map φ, ?_⟩
  rw [eval₂_map, hφ, ← hom_eval₂, hp, map_zero]

theorem isAlgebraic_of_smul {R A : Type*} [CommRing R] [IsDomain R] [Ring A] [Algebra R A] {z : A} {y : R}
    (hy : y ≠ 0) (h : IsAlgebraic R (y • z)) : IsAlgebraic R z :=
  IsAlgebraic.of_smul (mem_nonZeroDivisors_of_ne_zero hy) h

theorem main
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (𝔮 : Ideal B) [𝔮.IsPrime] :
    ∃ s : A, s ∉ 𝔮.under A ∧ ∀ (𝔔 : Ideal B) [𝔔.IsPrime], 𝔮 ≤ 𝔔 → s ∉ 𝔔.under A →
      Algebra.trdeg (A ⧸ 𝔔.under A) (B ⧸ 𝔔) ≤ Algebra.trdeg (A ⧸ 𝔮.under A) (B ⧸ 𝔮) := by
  classical
  set 𝔭 := 𝔮.under A with h𝔭

  haveI : Algebra.FiniteType (A ⧸ 𝔭) (B ⧸ 𝔮) := inferInstance
  obtain ⟨r, hr, d, z, hz, hint⟩ :=
    Algebra.exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType
      (R := A ⧸ 𝔭) (C := B ⧸ 𝔮)
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hs : s ∉ 𝔭 := fun h => hr (Ideal.Quotient.eq_zero_iff_mem.mpr h)
  refine ⟨s, hs, ?_⟩
  intro 𝔔 _ h𝔮𝔔 hs𝔔

  have hd : (d : Cardinal) ≤ Algebra.trdeg (A ⧸ 𝔭) (B ⧸ 𝔮) := by
    simpa using hz.lift_cardinalMk_le_trdeg
  refine le_trans ?_ hd

  set 𝔭' := 𝔔.under A with h𝔭'
  have h𝔭𝔭' : 𝔭 ≤ 𝔭' := Ideal.comap_mono h𝔮𝔔
  let πR : A ⧸ 𝔭 →+* A ⧸ 𝔭' := Ideal.Quotient.factor h𝔭𝔭'
  let πC : B ⧸ 𝔮 →+* B ⧸ 𝔔 := Ideal.Quotient.factor h𝔮𝔔
  have hπ : ∀ x : A ⧸ 𝔭, πC (algebraMap (A ⧸ 𝔭) (B ⧸ 𝔮) x) = algebraMap (A ⧸ 𝔭') (B ⧸ 𝔔) (πR x) := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  have hr' : πR (Ideal.Quotient.mk 𝔭 s) ≠ 0 := by
    change Ideal.Quotient.mk 𝔭' s ≠ 0
    exact fun h => hs𝔔 (Ideal.Quotient.eq_zero_iff_mem.mp h)

  let z' : Fin d → B ⧸ 𝔔 := fun i => πC (z i)
  let D : Subalgebra (A ⧸ 𝔭) (B ⧸ 𝔮) := Algebra.adjoin (A ⧸ 𝔭) (Set.range z)
  let D' : Subalgebra (A ⧸ 𝔭') (B ⧸ 𝔔) := Algebra.adjoin (A ⧸ 𝔭') (Set.range z')
  have hDD' : ∀ x ∈ D, πC x ∈ D' := by
    intro x hx
    refine Algebra.adjoin_induction (hx := hx) ?_ ?_ ?_ ?_
    · rintro _ ⟨i, rfl⟩; exact Algebra.subset_adjoin ⟨i, rfl⟩
    · intro x; rw [hπ]; exact Subalgebra.algebraMap_mem _ _
    · intro x y _ _ hx hy; rw [map_add]; exact D'.add_mem hx hy
    · intro x y _ _ hx hy; rw [map_mul]; exact D'.mul_mem hx hy

  haveI : Algebra.IsAlgebraic D' (B ⧸ 𝔔) := by
    refine ⟨fun c' => ?_⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.factor_surjective h𝔮𝔔 c'
    change IsAlgebraic D' (πC c)
    obtain ⟨n, hn⟩ := hint c
    have h1 : IsIntegral D' (πC ((Ideal.Quotient.mk 𝔭 s) ^ n • c)) := isIntegral_map_of_forall_mem πC D D' hDD' hn
    simp only [Algebra.smul_def, map_pow, map_mul] at h1
    rw [hπ] at h1

    let ρ : D' := ⟨algebraMap (A ⧸ 𝔭') (B ⧸ 𝔔) (πR (Ideal.Quotient.mk 𝔭 s)) ^ n,
      D'.pow_mem (Subalgebra.algebraMap_mem _ _) n⟩
    have hρ : (ρ : B ⧸ 𝔔) ≠ 0 := by
      refine pow_ne_zero _ ?_
      rw [Ne, ← map_zero (algebraMap (A ⧸ 𝔭') (B ⧸ 𝔔)),
        (FaithfulSMul.algebraMap_injective (A ⧸ 𝔭') (B ⧸ 𝔔)).eq_iff]
      exact hr'
    have hρ' : ρ ≠ 0 := fun h => hρ (by rw [h]; rfl)
    have h2 : IsAlgebraic D' (ρ • πC c) := by
      rw [Algebra.smul_def]
      exact h1.isAlgebraic
    exact isAlgebraic_of_smul hρ' h2
  have hrange : Cardinal.mk (Set.range z') ≤ (d : Cardinal.{v}) := by
    simpa using Cardinal.mk_range_le_lift (f := z')
  exact (Algebra.IsAlgebraic.trdeg_le_cardinalMk (A ⧸ 𝔭') (Set.range z')).trans hrange

end P2mGenericTrdegBound

theorem solution
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (𝔮 : Ideal B) [𝔮.IsPrime] :
    ∃ s : A, s ∉ 𝔮.under A ∧ ∀ (𝔔 : Ideal B) [𝔔.IsPrime], 𝔮 ≤ 𝔔 → s ∉ 𝔔.under A →
      Algebra.trdeg (A ⧸ 𝔔.under A) (B ⧸ 𝔔) ≤ Algebra.trdeg (A ⧸ 𝔮.under A) (B ⧸ 𝔮) :=
  P2mGenericTrdegBound.main 𝔮


end P2MW.S_Algebra_FiniteType_exists_notMem_under_forall_trdeg_quotient_le
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
