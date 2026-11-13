import ZInQKernel.Contrib.AbVarBC.Torsion
import ZInQKernel.Contrib.AbVarBC.Mul

/-!
# Base change of abelian varieties, VIII: tangent vectors as dual-number points

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task g9-abvarbc, 2026-11-13).

§1 For an affine open `U` of a scheme `X` and a local ring `Λ`, a morphism `p : Spec Λ → X`
sending the closed point into `U` is the same as a ring map `ptRing p : Γ(X, U) → Λ`
(`eq_ofRing_ptRing`, `ptRing_ofRing`, `ptRing_specMap_comp`, `ptRing_comp`).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

noncomputable section

namespace ZInQ.Contrib.AbVarBC.Tangent

/-! ## §1. Points of an affine open -/

section Gen

variable {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
  {Λ : CommRingCat.{0}} [IsLocalRing Λ]

/-- The ring map `Γ(X, U) → Λ` of a `Λ`-point whose closed point lies in `U`. -/
def ptRing (p : Spec Λ ⟶ X) (hp : p (IsLocalRing.closedPoint Λ) ∈ U) : Γ(X, U) ⟶ Λ :=
  p.appLE U ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem p hp).ge ≫ (Scheme.ΓSpecIso Λ).hom

theorem ptRing_congr {p q : Spec Λ ⟶ X} (e : p = q) (hp : p (IsLocalRing.closedPoint Λ) ∈ U)
    (hq : q (IsLocalRing.closedPoint Λ) ∈ U) : ptRing p hp = ptRing q hq := by
  subst e; rfl

/-- The point attached to a ring map `Γ(X, U) → Λ`. -/
def ofRing (φ : Γ(X, U) ⟶ Λ) : Spec Λ ⟶ X := Spec.map φ ≫ hU.fromSpec

theorem ofRing_mem (φ : Γ(X, U) ⟶ Λ) : ofRing hU φ (IsLocalRing.closedPoint Λ) ∈ U := by
  change ofRing hU φ _ ∈ (U : Set X)
  rw [← hU.range_fromSpec]
  exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩

theorem eq_ofRing_ptRing (p : Spec Λ ⟶ X) (hp : p (IsLocalRing.closedPoint Λ) ∈ U) :
    p = ofRing hU (ptRing p hp) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec p hU (isAffineOpen_top _)
    (Scheme.preimage_eq_top_of_closedPoint_mem p hp).ge
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [ofRing, ptRing, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem ptRing_ext (hU : IsAffineOpen U) {p q : Spec Λ ⟶ X} (hp : p (IsLocalRing.closedPoint Λ) ∈ U)
    (hq : q (IsLocalRing.closedPoint Λ) ∈ U) (h : ptRing p hp = ptRing q hq) : p = q := by
  rw [eq_ofRing_ptRing hU p hp, eq_ofRing_ptRing hU q hq, h]

theorem ptRing_ofRing (φ : Γ(X, U) ⟶ Λ) : ptRing (ofRing hU φ) (ofRing_mem hU φ) = φ := by
  have h := eq_ofRing_ptRing hU (ofRing hU φ) (ofRing_mem hU φ)
  unfold ofRing at h
  rw [cancel_mono] at h
  exact (Spec.map_injective h).symm

/-- Naturality in the local ring. -/
theorem ptRing_specMap_comp (hU : IsAffineOpen U) {Λ' : CommRingCat.{0}} [IsLocalRing Λ'] (ρ : Λ ⟶ Λ')
    (p : Spec Λ ⟶ X) (hp : p (IsLocalRing.closedPoint Λ) ∈ U)
    (hp' : (Spec.map ρ ≫ p) (IsLocalRing.closedPoint Λ') ∈ U) :
    ptRing (Spec.map ρ ≫ p) hp' = ptRing p hp ≫ ρ := by
  have e : Spec.map ρ ≫ p = ofRing hU (ptRing p hp ≫ ρ) := by
    conv_lhs => rw [eq_ofRing_ptRing hU p hp]
    rw [ofRing, ofRing, ← Category.assoc, ← Spec.map_comp]
  rw [ptRing_congr e hp' (ofRing_mem hU _), ptRing_ofRing]

/-- Naturality in the scheme. -/
theorem ptRing_comp (hU : IsAffineOpen U) {Y : Scheme.{0}} (f : X ⟶ Y) {U' : Y.Opens} (hU' : IsAffineOpen U')
    (hle : U ≤ f ⁻¹ᵁ U') (p : Spec Λ ⟶ X) (hp : p (IsLocalRing.closedPoint Λ) ∈ U)
    (hp' : (p ≫ f) (IsLocalRing.closedPoint Λ) ∈ U') :
    ptRing (p ≫ f) hp' = f.appLE U' U hle ≫ ptRing p hp := by
  have e : p ≫ f = ofRing hU' (f.appLE U' U hle ≫ ptRing p hp) := by
    conv_lhs => rw [eq_ofRing_ptRing hU p hp]
    rw [ofRing, ofRing, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU' hU hle,
      ← Category.assoc, ← Spec.map_comp]
  rw [ptRing_congr e hp' (ofRing_mem hU' _), ptRing_ofRing]

end Gen

end ZInQ.Contrib.AbVarBC.Tangent
