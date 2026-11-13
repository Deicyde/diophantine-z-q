import Mathlib
import ZInQKernel.HDecomp.Objects

/-!
# Base change of abelian varieties, II: points

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).
§1 is task unram-tate's `scratch/unram-tate/BCPoints.lean` (namespace `UnramTate`), moved into the
namespace `ZInQ.Contrib.AbVarBC`. §2 is new.

For the project's abelian varieties (`PkgI3.AbVar`, `ZInQKernel/HDecomp/Objects.lean`):
* `bcPt : (A.baseChange L).Pt Ω ≃* A.Pt Ω` (points of a base change), natural for
  `L`-automorphisms of `Ω` (`bcPt_galAct`);
* `extPt κ : A.Pt Ω →* A.Pt Ω₂` along a `K`-embedding of fields `κ : Ω →ₐ[K] Ω₂`, **injective**
  (`extPt_injective`: `Spec Ω₂ → Spec Ω` is faithfully flat and quasi-compact, hence an effective
  epimorphism, Mathlib's Stacks 023Q), and Galois-natural (`extPt_galAct`).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

set_option linter.style.haveILetI false

namespace ZInQ.Contrib.AbVarBC

/-! ## §1. Points of a base change (task unram-tate) -/

/-- `Spec L → Spec K`. -/
noncomputable abbrev sK (K L : Type) [Field K] [Field L] [Algebra K L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K L))

section BC

variable {K L : Type} [Field K] [Field L] [Algebra K L] (A : PkgI3.AbVar K)
  (Ω : Type) [Field Ω] [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω]

theorem specMap_comp_sK :
    Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ sK K L =
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsScalarTower.algebraMap_eq K L Ω]

/-- `Over.map (Spec L → Spec K) (Spec Ω / L) ≅ Spec Ω / K`. -/
noncomputable def ptMapIso :
    (Over.map (sK K L)).obj (PkgI3.AbVar.ptObj (K := L) Ω) ≅ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.isoMk (Iso.refl _) (by
    simp only [Over.map_obj_hom, Iso.refl_hom, PkgI3.AbVar.ptObj, Over.mk_hom]
    erw [Category.id_comp]
    exact (specMap_comp_sK (K := K) (L := L) Ω).symm)

/-- The adjunction bijection is multiplicative. -/
theorem homEquiv_mul (X : Over (Spec (CommRingCat.of L)))
    (p q : (Over.map (sK K L)).obj X ⟶ A.X) :
    (Over.mapPullbackAdj (sK K L)).homEquiv X A.X (p * q) =
      (Over.mapPullbackAdj (sK K L)).homEquiv X A.X p *
        (Over.mapPullbackAdj (sK K L)).homEquiv X A.X q := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Functor.map_mul, MonObj.comp_mul]

/-- **Points of a base change**: `A_L(Ω) ≃* A(Ω)`. -/
noncomputable def bcPt : (A.baseChange L).Pt Ω ≃* A.Pt Ω where
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

/-- `bcPt` is natural for `L`-automorphisms of `Ω`. -/
theorem bcPt_galAct (σ : Ω ≃ₐ[L] Ω) (p : (A.baseChange L).Pt Ω) :
    bcPt A Ω ((A.baseChange L).galAct σ p) = A.galAct (σ.restrictScalars K) (bcPt A Ω p) := by
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

section Tr

variable {K : Type} [Field K] (A : PkgI3.AbVar K)
  {Ω Ω₂ : Type} [Field Ω] [Algebra K Ω] [Field Ω₂] [Algebra K Ω₂]

/-- `Spec Ω₂ → Spec Ω` over `K`, for a `K`-isomorphism `φ : Ω ≃ Ω₂`. -/
noncomputable def trHom (φ : Ω ≃ₐ[K] Ω₂) :
    PkgI3.AbVar.ptObj (K := K) Ω₂ ⟶ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.homMk (Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂))) (by
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

theorem trHom_left (φ : Ω ≃ₐ[K] Ω₂) :
    (trHom φ).left = Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) := rfl

theorem trHom_symm_comp (φ : Ω ≃ₐ[K] Ω₂) : trHom φ.symm ≫ trHom φ = 𝟙 _ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (φ.symm : Ω₂ →+* Ω)) ≫
    Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) = 𝟙 (Spec (CommRingCat.of Ω))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    show (φ.symm : Ω₂ →+* Ω).comp (φ : Ω →+* Ω₂) = RingHom.id Ω by ext x; simp,
    CommRingCat.ofHom_id, Spec.map_id]

theorem trHom_comp_symm (φ : Ω ≃ₐ[K] Ω₂) : trHom φ ≫ trHom φ.symm = 𝟙 _ := by
  simpa using trHom_symm_comp φ.symm

/-- **Transport of points** along `φ : Ω ≃ₐ[K] Ω₂`. -/
noncomputable def trPt (φ : Ω ≃ₐ[K] Ω₂) : A.Pt Ω ≃* A.Pt Ω₂ where
  toFun p := trHom φ ≫ p
  invFun x := trHom φ.symm ≫ x
  left_inv p := by simp [← Category.assoc, trHom_symm_comp]
  right_inv x := by simp [← Category.assoc, trHom_comp_symm]
  map_mul' p q := MonObj.comp_mul _ _ _

/-- `trPt φ` carries the action of `σ` to that of `φσφ⁻¹`. -/
theorem trPt_galAct (φ : Ω ≃ₐ[K] Ω₂) (σ : Ω ≃ₐ[K] Ω) (σ₂ : Ω₂ ≃ₐ[K] Ω₂)
    (h : ∀ x, σ₂ (φ x) = φ (σ x)) (p : A.Pt Ω) :
    trPt A φ (A.galAct σ p) = A.galAct σ₂ (trPt A φ p) := by
  show trHom φ ≫ PkgI3.AbVar.galHom σ ≫ p = PkgI3.AbVar.galHom σ₂ ≫ trHom φ ≫ p
  have hsq : trHom φ ≫ PkgI3.AbVar.galHom σ = PkgI3.AbVar.galHom σ₂ ≫ trHom φ := by
    apply Over.OverMorphism.ext
    change Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂)) ≫
        Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω)) =
      Spec.map (CommRingCat.ofHom (σ₂ : Ω₂ →+* Ω₂)) ≫ Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω₂))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    exact (h x).symm
  rw [← Category.assoc, ← Category.assoc, hsq]

end Tr

/-! ## §2. Points over an extension of fields -/

section Ext

variable {K : Type} [Field K] (A : PkgI3.AbVar K)
  {Ω Ω₂ : Type} [Field Ω] [Algebra K Ω] [Field Ω₂] [Algebra K Ω₂]

/-- `Spec Ω₂ → Spec Ω` over `K`, for a `K`-embedding `κ : Ω → Ω₂`. -/
noncomputable def extHom (κ : Ω →ₐ[K] Ω₂) :
    PkgI3.AbVar.ptObj (K := K) Ω₂ ⟶ PkgI3.AbVar.ptObj (K := K) Ω :=
  Over.homMk (Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂))) (by
    simp only [PkgI3.AbVar.ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

theorem extHom_left (κ : Ω →ₐ[K] Ω₂) :
    (extHom κ).left = Spec.map (CommRingCat.ofHom (κ : Ω →+* Ω₂)) := rfl

/-- `Spec` of a map of fields is an epimorphism of schemes (faithfully flat, quasi-compact). -/
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

/-- **Points along a field extension**: `A(Ω) → A(Ω₂)`, `p ↦ p ∘ Spec κ`. -/
noncomputable def extPt (κ : Ω →ₐ[K] Ω₂) : A.Pt Ω →* A.Pt Ω₂ where
  toFun p := extHom κ ≫ p
  map_one' := MonObj.comp_one _
  map_mul' p q := MonObj.comp_mul _ _ _

theorem extPt_apply (κ : Ω →ₐ[K] Ω₂) (p : A.Pt Ω) : extPt A κ p = extHom κ ≫ p := rfl

/-- **`A(Ω) → A(Ω₂)` is injective.** -/
theorem extPt_injective (κ : Ω →ₐ[K] Ω₂) : Function.Injective (extPt A κ) :=
  fun _ _ h => (cancel_epi (extHom κ)).1 h

/-- `extPt κ` carries the action of `τ ∈ Aut_K(Ω)` to that of `σ ∈ Aut_K(Ω₂)` when
`κ ∘ τ = σ ∘ κ`. -/
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

end ZInQ.Contrib.AbVarBC
