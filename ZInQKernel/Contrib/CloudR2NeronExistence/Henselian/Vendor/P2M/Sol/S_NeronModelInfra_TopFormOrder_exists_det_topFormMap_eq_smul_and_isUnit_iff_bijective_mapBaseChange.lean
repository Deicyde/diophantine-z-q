import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_NeronModelInfra_TopFormOrder_exists_det_topFormMap_eq_smul_and_isUnit_iff_bijective_mapBaseChange.lean
Original Git blob: 109487c12b528cd96c5325533ea53e2894a0f30a
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "TensorProduct"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_NeronModelInfra_TopFormOrder_exists_det_topFormMap_eq_smul_and_isUnit_iff_bijective_mapBaseChange
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open NeronModelInfra.TopFormOrder

namespace OCBTop
h77_bridge_namespace

open Set Set.powersetCard

@[reducible] noncomputable def uniquePowersetCardFin (n : ℕ) : Unique (Set.powersetCard (Fin n) n) where
  default := Set.powersetCard.ofCard (n := n) (s := (Finset.univ : Finset (Fin n))) (by simp)
  uniq s := Subtype.ext (Finset.eq_univ_of_card _ (by
    rw [Fintype.card_fin]; exact Set.powersetCard.card_eq s))

variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M] {n : ℕ}

lemma exists_basis_exteriorPower_top (b : Module.Basis (Fin n) A M) :
    ∃ B : Module.Basis (Set.powersetCard (Fin n) n) A (⋀[A]^n M), ∀ s, B s = exteriorPower.ιMulti A n b := by
  letI := uniquePowersetCardFin n
  let φ : Fin n ↪o Fin n := ofFinEmbEquiv.symm (default : Set.powersetCard (Fin n) n)
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective φ (Finite.injective_iff_bijective.1 φ.injective)
  refine ⟨(b.reindex σ).exteriorPower n, fun s => ?_⟩
  rw [Subsingleton.elim s default, exteriorPower.basis_apply]
  change exteriorPower.ιMulti A n ((b.reindex σ) ∘ σ) = _
  congr 1
  funext i
  simp

lemma exists_eq_smul_ιMulti (b : Module.Basis (Fin n) A M) (x : ⋀[A]^n M) :
    ∃ r : A, x = r • exteriorPower.ιMulti A n b := by
  letI := uniquePowersetCardFin n
  obtain ⟨B, hB⟩ := exists_basis_exteriorPower_top b
  refine ⟨B.repr x default, ?_⟩
  conv_lhs => rw [← B.sum_repr x]
  rw [Fintype.sum_unique, hB]

end OCBTop

open scoped _root_.TensorProduct

namespace OCC
h77_bridge_namespace

lemma ιMulti_eq_det_smul {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M] {n : ℕ}
    (b : Module.Basis (Fin n) A M) (w : Fin n → M) :
    exteriorPower.ιMulti A n w = b.det w • exteriorPower.ιMulti A n b := by
  classical
  obtain ⟨r, hr⟩ := OCBTop.exists_eq_smul_ιMulti b (exteriorPower.ιMulti A n w)
  have h := congrArg (exteriorPower.alternatingMapLinearEquiv b.det) hr
  rw [map_smul, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, Module.Basis.det_self, smul_eq_mul, mul_one] at h
  rw [hr, h]

lemma map_map (R' K' O' O F : Type u) [CommRing R'] [CommRing K'] [Algebra R' K']
    [CommRing O'] [Algebra R' O'] [CommRing O] [Algebra R' O] [Algebra O' O] [IsScalarTower R' O' O]
    [CommRing F] [Algebra O F] [Algebra O' F] [IsScalarTower O' O F] [Algebra K' F] [Algebra R' F]
    [IsScalarTower R' O F] [IsScalarTower R' O' F] [IsScalarTower R' K' F]
    (x : Ω[O'⁄R']) :
    KaehlerDifferential.map R' K' O F (KaehlerDifferential.map R' R' O' O x) =
      KaehlerDifferential.map R' K' O' F x := by
  have key : ∀ x ∈ Submodule.span O' (Set.range (KaehlerDifferential.D R' O')),
      KaehlerDifferential.map R' K' O F (KaehlerDifferential.map R' R' O' O x) =
        KaehlerDifferential.map R' K' O' F x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, rfl⟩ := hy
      rw [KaehlerDifferential.map_D, KaehlerDifferential.map_D, KaehlerDifferential.map_D,
        ← IsScalarTower.algebraMap_apply]
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, map_add, map_add, hy, hz]
    | smul s y _ hy =>
      rw [(KaehlerDifferential.map R' R' O' O).map_smul s y, (KaehlerDifferential.map R' K' O' F).map_smul s y,
        ← hy, ← IsScalarTower.algebraMap_smul O s ((KaehlerDifferential.map R' R' O' O) y),
        (KaehlerDifferential.map R' K' O F).map_smul,
        ← IsScalarTower.algebraMap_smul F (algebraMap O' O s), ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_smul]
  exact key x (by rw [KaehlerDifferential.span_range_derivation]; trivial)

end OCC


theorem solution
    (R' K' O' O F : Type u) [CommRing R'] [CommRing K'] [Algebra R' K']
    [CommRing O'] [Algebra R' O'] [CommRing O] [Algebra R' O] [Algebra O' O] [IsScalarTower R' O' O]
    [CommRing F] [Algebra O F] [Algebra O' F] [IsScalarTower O' O F] [Algebra K' F] [Algebra R' F]
    [IsScalarTower R' O F] [IsScalarTower R' O' F] [IsScalarTower R' K' F]
    (d : ℕ) (b' : Module.Basis (Fin d) O' (Ω[O'⁄R'])) (b : Module.Basis (Fin d) O (Ω[O⁄R'])) :
    ∃ h : O,
      (letI := moduleAlong O' F (⋀[F]^d (Ω[F⁄K']))
       letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
       topFormMap R' K' O' F d (exteriorPower.ιMulti O' d b') =
         algebraMap O F h • topFormMap R' K' O F d (exteriorPower.ιMulti O d b)) ∧
      (IsUnit h ↔ Function.Bijective (KaehlerDifferential.mapBaseChange R' O' O)) := by
  classical

  let φ : Ω[O'⁄R'] →ₗ[O'] Ω[O⁄R'] := KaehlerDifferential.map R' R' O' O
  let w : Fin d → Ω[O⁄R'] := fun j => φ (b' j)
  refine ⟨b.det w, ?_, ?_⟩
  · letI instO' := moduleAlong O' F (⋀[F]^d (Ω[F⁄K']))
    letI instO := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))

    have h1 : topFormMap R' K' O F d (exteriorPower.ιMulti O d w) =
        b.det w • topFormMap R' K' O F d (exteriorPower.ιMulti O d b) := by
      rw [OCC.ιMulti_eq_det_smul b w, map_smul]

    have h2 : topFormMap R' K' O F d (exteriorPower.ιMulti O d w) =
        topFormMap R' K' O' F d (exteriorPower.ιMulti O' d b') := by
      show exteriorPower.alternatingMapLinearEquiv (ιMultiAlong R' K' O F d) (exteriorPower.ιMulti O d w) =
        exteriorPower.alternatingMapLinearEquiv (ιMultiAlong R' K' O' F d) (exteriorPower.ιMulti O' d b')
      rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
      show exteriorPower.ιMulti F d (fun i => KaehlerDifferential.map R' K' O F (w i)) =
        exteriorPower.ιMulti F d (fun i => KaehlerDifferential.map R' K' O' F (b' i))
      congr 1
      funext i
      exact OCC.map_map R' K' O' O F (b' i)
    rw [← h2, h1]
    rfl
  ·
    let Φ := KaehlerDifferential.mapBaseChange R' O' O
    let bO := Algebra.TensorProduct.basis O b'
    have hmat : b.toMatrix w = LinearMap.toMatrix bO b Φ := by
      ext i j
      rw [Module.Basis.toMatrix_apply, LinearMap.toMatrix_apply]
      congr 2
      show φ (b' j) = KaehlerDifferential.mapBaseChange R' O' O (Algebra.TensorProduct.basis O b' j)
      rw [Algebra.TensorProduct.basis_apply, KaehlerDifferential.mapBaseChange_tmul, one_smul]
    rw [Module.Basis.det_apply, hmat]
    constructor
    · intro hu
      have hcoe : ((LinearEquiv.ofIsUnitDet (f := Φ) (v := bO) (v' := b) hu : O ⊗[O'] Ω[O'⁄R'] ≃ₗ[O] Ω[O⁄R']) :
          O ⊗[O'] Ω[O'⁄R'] →ₗ[O] Ω[O⁄R']) = Φ := LinearEquiv.coe_ofIsUnitDet hu
      have : Function.Bijective (LinearEquiv.ofIsUnitDet (f := Φ) (v := bO) (v' := b) hu) :=
        (LinearEquiv.ofIsUnitDet (f := Φ) (v := bO) (v' := b) hu).bijective
      rwa [← LinearEquiv.coe_coe, hcoe] at this
    · intro hb
      have := LinearEquiv.isUnit_det (LinearEquiv.ofBijective Φ hb) bO b
      exact this


end P2MW.S_NeronModelInfra_TopFormOrder_exists_det_topFormMap_eq_smul_and_isUnit_iff_bijective_mapBaseChange
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
