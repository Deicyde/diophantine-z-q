import Mathlib
import ZInQKernel.HDecomp.Objects

/-!
# Universe-generic transport of the fixed Raynaud point objects

Derived from `ZInQKernel/Contrib/AbVarBC/Points.lean` at
`df98652abbeeef78b57f0868f19523a26d811b58` (task g9-abvarbc, 2026-11-13),
whose first section derives from task unram-tate's `BCPoints.lean`.
Original copyright: this file is part of Deicyde/diophantine-z-q.
Modification notice (H4 round 2, 2026-11-14): all fields/schemes live in the
same arbitrary universe `u`; the namespace is isolated. The maps remain the
literal `Spec.map`/`Over.mapPullbackAdj` maps of the fixed object layer.

These are transport lemmas, NOT a proof of `PkgI2.RaynaudCriterion`.
No semistability, Néron existence, monodromy or rational-torsion hypothesis
is asserted as a theorem in this file.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

set_option linter.style.haveILetI false

universe u

namespace ZInQ.Contrib.CloudR2Raynaud.GenericPoints

/-- The actual base-field map `Spec L → Spec K`. -/
abbrev sK (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

/-- Universe-generic packaging of the literal fixed `Over.pullback` base change.
The original `PkgI3.AbVar.baseChange` is restricted to universe zero. -/
def baseChange {K : Type u} [Field K] (A : PkgI3.AbVar K)
    (L : Type u) [Field L] [Algebra K L] : PkgI3.AbVar L :=
  let f := Spec.map (CommRingCat.ofHom (algebraMap K L))
  letI : GrpObj ((Over.pullback f).obj A.X) := Functor.grpObjObj
  haveI : IsProper ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : Smooth ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral ((Over.pullback f).obj A.X).hom := by dsimp; infer_instance
  { X := (Over.pullback f).obj A.X }

section BC

variable {K L : Type u} [Field K] [Field L] [Algebra K L] (A : PkgI3.AbVar K)
  (Ω : Type u) [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]

theorem specMap_comp_sK :
    Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ sK K L =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq K L Ω]

/-- The actual point-source identification, with underlying scheme identity. -/
def ptMapIso :
    (Over.map (sK K L)).obj (PkgI3.AbVar.ptObj (K := L) Ω) ≅ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.isoMk (Iso.refl _) (by
    simp only [Over.map_obj_hom, Iso.refl_hom, PkgI3.AbVar.ptObj, Over.mk_hom]
    erw [Category.id_comp]
    exact (specMap_comp_sK (K := K) (L := L) Ω).symm)

theorem homEquiv_mul (X : Over (Spec (CommRingCat.of L)))
    (p q : (Over.map (sK K L)).obj X ⟶ A.X) :
    (Over.mapPullbackAdj (sK K L)).homEquiv X A.X (p * q) =
      (Over.mapPullbackAdj (sK K L)).homEquiv X A.X p *
        (Over.mapPullbackAdj (sK K L)).homEquiv X A.X q := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

/-- Points of the genuine base change, not of a substitute group. -/
def bcPt : (baseChange A L).Pt Ω ≃* A.Pt Ω where
  toFun p := (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm p
  invFun x := (Over.mapPullbackAdj (sK K L)).homEquiv _ _ ((ptMapIso Ω).hom ≫ x)
  left_inv p := Equiv.apply_symm_apply ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X) p
  right_inv x := by
    show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
      ((Over.mapPullbackAdj (sK K L)).homEquiv _ _ ((ptMapIso Ω).hom ≫ x)) = x
    rw [Equiv.symm_apply_apply, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  map_mul' p q := by
    obtain ⟨p', rfl⟩ := ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X).surjective p
    obtain ⟨q', rfl⟩ := ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X).surjective q
    show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
        ((Over.mapPullbackAdj (sK K L)).homEquiv _ A.X p' *
          (Over.mapPullbackAdj (sK K L)).homEquiv _ A.X q') = _
    rw [← homEquiv_mul, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      MonObj.comp_mul]

/-- Semilinear Galois naturality on the original geometric point scheme. -/
theorem bcPt_galAct (σ : Ω ≃ₐ[L] Ω) (p : (baseChange A L).Pt Ω) :
    bcPt A Ω ((baseChange A L).galAct σ p) = A.galAct (σ.restrictScalars K) (bcPt A Ω p) := by
  show (ptMapIso Ω).inv ≫ ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm
      (PkgI3.AbVar.galHom σ ≫ p) =
    PkgI3.AbVar.galHom (σ.restrictScalars K) ≫ (ptMapIso Ω).inv ≫
      ((Over.mapPullbackAdj (sK K L)).homEquiv _ _).symm p
  have hnat := Adjunction.homEquiv_naturality_left_symm (Over.mapPullbackAdj (sK K L))
    (PkgI3.AbVar.galHom σ) (p : PkgI3.AbVar.ptObj Ω ⟶ (Over.pullback (sK K L)).obj A.X)
  have hsq : (ptMapIso Ω).inv ≫ (Over.map (sK K L)).map (PkgI3.AbVar.galHom σ) =
      PkgI3.AbVar.galHom (σ.restrictScalars K) ≫ (ptMapIso Ω).inv := by
    apply Over.OverMorphism.ext
    simp [ptMapIso, PkgI3.AbVar.galHom]
    rfl
  erw [hnat]
  rw [← Category.assoc, hsq, Category.assoc]

end BC

section Ext

variable {K : Type u} [Field K] (A : PkgI3.AbVar K)
  {Ω Ω₂ : Type u} [Field Ω] [Algebra K Ω] [Field Ω₂] [Algebra K Ω₂]

/-- Literal precomposition map on point sources for a field embedding. -/
def extHom (κ : Ω →ₐ[K] Ω₂) :
    PkgI3.AbVar.ptObj (K := K) Ω₂ ⟶ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.homMk (Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂))) (by
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

theorem extHom_left (κ : Ω →ₐ[K] Ω₂) :
    (extHom κ).left = Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)) := rfl

/-- Spec of a field embedding is faithfully flat and quasi-compact, hence epi. -/
theorem epi_spec_map_field (κ : Ω →+* Ω₂) : Epi (Spec.map (CommRingCat.ofHom κ)) := by
  haveI : Surjective (Spec.map (CommRingCat.ofHom κ)) := by
    constructor
    intro y
    refine ⟨IsLocalRing.closedPoint Ω₂, Subsingleton.elim _ _⟩
  haveI : Flat (Spec.map (CommRingCat.ofHom κ)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    algebraize [κ]
    change Module.Flat Ω Ω₂
    infer_instance
  infer_instance

instance epi_extHom (κ : Ω →ₐ[K] Ω₂) : Epi (extHom κ) := by
  haveI : Epi ((Over.forget _).map (extHom κ)) := epi_spec_map_field (κ : Ω →+* Ω₂)
  exact (Over.forget _).epi_of_epi_map this

def extPt (κ : Ω →ₐ[K] Ω₂) : A.Pt Ω →* A.Pt Ω₂ where
  toFun p := extHom κ ≫ p
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

theorem extPt_apply (κ : Ω →ₐ[K] Ω₂) (p : A.Pt Ω) : extPt A κ p = extHom κ ≫ p := rfl

theorem extPt_injective (κ : Ω →ₐ[K] Ω₂) : Function.Injective (extPt A κ) :=
  fun _ _ h => (cancel_epi (extHom κ)).1 h

theorem extPt_galAct (κ : Ω →ₐ[K] Ω₂) (τ : Ω ≃ₐ[K] Ω) (σ : Ω₂ ≃ₐ[K] Ω₂)
    (h : ∀ x, κ (τ x) = σ (κ x)) (p : A.Pt Ω) :
    extPt A κ (A.galAct τ p) = A.galAct σ (extPt A κ p) := by
  show extHom κ ≫ PkgI3.AbVar.galHom τ ≫ p = PkgI3.AbVar.galHom σ ≫ extHom κ ≫ p
  have hsq : extHom κ ≫ PkgI3.AbVar.galHom τ = PkgI3.AbVar.galHom σ ≫ extHom κ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)) ≫
        Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω)) =
      Spec.map (CommRingCat.ofHom (σ : Ω₂ →+* Ω₂)) ≫ Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact (h x)
  rw [← Category.assoc, ← Category.assoc, hsq]

end Ext

section FixedObject

variable {K : Type u} [Field K]

/-- I3 packaging of the fixed I2 object, retaining its scheme and group law definitionally. -/
def ofFixedGrp (A : Grp (Over (Spec (.of K)))) [h : PkgI2.IsAbelianVariety A] : PkgI3.AbVar K :=
  haveI := h.proper
  haveI := h.smooth
  haveI := h.geomIntegral
  { X := A.X }

@[simp] theorem ofFixedGrp_X (A : Grp (Over (Spec (.of K)))) [PkgI2.IsAbelianVariety A] :
    (ofFixedGrp A).X = A.X := rfl

theorem fixed_pts_eq (A : Grp (Over (Spec (.of K)))) [PkgI2.IsAbelianVariety A]
    (Ω : Type u) [Field Ω] [Algebra K Ω] : PkgI2.Pts A Ω = (ofFixedGrp A).Pt Ω := rfl

theorem fixed_galAct_eq (A : Grp (Over (Spec (.of K)))) [PkgI2.IsAbelianVariety A]
    {Ω : Type u} [Field Ω] [Algebra K Ω] (σ : Ω ≃ₐ[K] Ω) (x : PkgI2.Pts A Ω) :
    PkgI2.galAct A σ x = (ofFixedGrp A).galAct σ x := rfl

/-- Transport the literal `(σ−1)²` expression, rather than a scalar/example surrogate. -/
theorem square_expression_bc (A : PkgI3.AbVar K) {L Ω : Type u} [Field L] [Algebra K L]
    [Field Ω] [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω]
    (σ : Ω ≃ₐ[L] Ω) (x : (baseChange A L).Pt Ω) :
    bcPt A Ω ((baseChange A L).galAct σ ((baseChange A L).galAct σ x) *
      ((baseChange A L).galAct σ x)⁻¹ * ((baseChange A L).galAct σ x)⁻¹ * x) =
    A.galAct (σ.restrictScalars K) (A.galAct (σ.restrictScalars K) (bcPt A Ω x)) *
      (A.galAct (σ.restrictScalars K) (bcPt A Ω x))⁻¹ *
      (A.galAct (σ.restrictScalars K) (bcPt A Ω x))⁻¹ * bcPt A Ω x := by
  simp only [map_mul, map_inv, bcPt_galAct]

end FixedObject

end ZInQ.Contrib.CloudR2Raynaud.GenericPoints
