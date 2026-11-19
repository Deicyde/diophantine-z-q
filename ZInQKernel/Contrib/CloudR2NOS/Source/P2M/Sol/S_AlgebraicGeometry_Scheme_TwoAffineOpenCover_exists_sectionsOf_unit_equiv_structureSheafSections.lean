/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections.lean
  Source sha256  : de0bf8f1e15893352e47cd3b1f918c52bb26541aa9104516788e72129de51afe
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 5 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: T7×2; rule citations in the batch ledger.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections
r2nos_namespace_dual

set_option autoImplicit false

noncomputable section

universe u

w03_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections.AlgebraicGeometry Opposite"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Spec Scheme Scheme.TwoAffineOpenCover"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "ringCatSheaf mk Modules Cover TwoAffineOpenCover"
namespace TwoAffineOpenCover
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "sectionsOf cover structureSheafSections mk"
w03_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"
namespace UnitComparison
r2nos_namespace_dual

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
    rw [← cechDiff_eq, hx]; rfl⟩

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

open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.TwoAffineOpenCover _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections.AlgebraicGeometry.Scheme.TwoAffineOpenCover in
r2nos_open_dual "_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.TwoAffineOpenCover _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections.AlgebraicGeometry.Scheme.TwoAffineOpenCover" in
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
end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
