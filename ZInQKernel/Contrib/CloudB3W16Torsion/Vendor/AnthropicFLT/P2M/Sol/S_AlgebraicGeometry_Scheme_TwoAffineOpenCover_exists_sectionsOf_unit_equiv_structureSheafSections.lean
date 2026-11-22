/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections

set_option autoImplicit false

noncomputable section

universe u
open CategoryTheory
open AlgebraicGeometry
-- Source P2M scope referred to a not-yet-declared local namespace; root scope retained.
open Opposite

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Spec Scheme Scheme.TwoAffineOpenCover)
namespace Scheme
export _root_.AlgebraicGeometry.Scheme (ringCatSheaf mk Modules Cover TwoAffineOpenCover)
namespace TwoAffineOpenCover
export _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover (sectionsOf cover structureSheafSections mk)
open AlgebraicGeometry.Scheme.TwoAffineOpenCover
open AlgebraicGeometry.Scheme
open AlgebraicGeometry
namespace UnitComparison

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))

abbrev SU : TwoChartCech.Sections (𝒱.cover c) := 𝒱.sectionsOf c (SheafOfModules.unit X.ringCatSheaf : X.Modules)
abbrev SO : TwoChartCech.Sections (𝒱.cover c) := 𝒱.structureSheafSections c

theorem cechDiff_eq (s : (SU 𝒱 c).M0 × (SU 𝒱 c).M1) :
    (show (SO 𝒱 c).M01 from (SU 𝒱 c).cechDiff s)
      = (SO 𝒱 c).cechDiff (show (SO 𝒱 c).M0 × (SO 𝒱 c).M1 from s) := by
  rw [TwoChartCech.Sections.cechDiff_apply, TwoChartCech.Sections.cechDiff_apply,
    TwoChartCech.Cover.lineBundle_r1_apply, TwoChartCech.Cover.lineBundle_r0_apply, Units.val_one, one_mul]
  rfl

def toFunH0 (x : (SU 𝒱 c).H0) : (SO 𝒱 c).H0 :=
  ⟨(show (SO 𝒱 c).M0 × (SO 𝒱 c).M1 from x.1), by
    have hx := x.2
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← cechDiff_eq, hx]⟩

def invFunH0 (x : (SO 𝒱 c).H0) : (SU 𝒱 c).H0 :=
  ⟨(show (SU 𝒱 c).M0 × (SU 𝒱 c).M1 from x.1), by
    have hx := x.2
    rw [LinearMap.mem_ker] at hx ⊢
    have := cechDiff_eq 𝒱 c (show (SU 𝒱 c).M0 × (SU 𝒱 c).M1 from x.1)

    exact (show (SU 𝒱 c).cechDiff _ = (show (SU 𝒱 c).M01 from (0 : (SO 𝒱 c).M01)) from by rw [← hx]; exact this)⟩

def equivH0 : (SU 𝒱 c).H0 ≃ₗ[R] (SO 𝒱 c).H0 where
  toFun := toFunH0 𝒱 c
  invFun := invFunH0 𝒱 c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem range_eq :
    (show Submodule R (SO 𝒱 c).M01 from LinearMap.range (SU 𝒱 c).cechDiff) = LinearMap.range (SO 𝒱 c).cechDiff := by
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨(show (SO 𝒱 c).M0 × (SO 𝒱 c).M1 from s), (cechDiff_eq 𝒱 c s).symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨(show (SU 𝒱 c).M0 × (SU 𝒱 c).M1 from s), cechDiff_eq 𝒱 c _⟩

def equivH1 : (SU 𝒱 c).H1 ≃ₗ[R] (SO 𝒱 c).H1 :=
  Submodule.quotEquivOfEq _ _ (range_eq 𝒱 c)

end UnitComparison

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover _root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections.AlgebraicGeometry.Scheme.TwoAffineOpenCover in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R)) :
    ∃ (e0 : (𝒱.sectionsOf c (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 ≃ₗ[R]
          (𝒱.structureSheafSections c).H0)
      (e1 : (𝒱.sectionsOf c (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 ≃ₗ[R]
          (𝒱.structureSheafSections c).H1),
      (∀ x, ((e0 x : (𝒱.structureSheafSections c).M0 × (𝒱.structureSheafSections c).M1)) = x.1) ∧
      (∀ y : (𝒱.sectionsOf c (SheafOfModules.unit X.ringCatSheaf : X.Modules)).M01,
          e1 (Submodule.Quotient.mk y) = Submodule.Quotient.mk (show (𝒱.structureSheafSections c).M01 from y)) :=
  ⟨UnitComparison.equivH0 𝒱 c, UnitComparison.equivH1 𝒱 c, fun _ => rfl, fun _ => rfl⟩

end
