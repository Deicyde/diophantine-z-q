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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_baseChange_equiv_of_locallyTrivial.lean
  Source sha256  : 1a529a4099b098ee740a87384efae721d08a1c827114549dbd14b681b306a81c
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 5 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_baseChange_equiv_of_locallyTrivial
r2nos_namespace_dual
r2nos_erase_attr "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_baseChange_equiv_of_locallyTrivial.AlgebraicGeometry TensorProduct AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_baseChange_equiv_of_locallyTrivial.AlgebraicGeometry.Scheme.TwoAffineOpenCover"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.Modules.pullback Spec Scheme Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pullback Γ Modules.pullbackPushforwardAdjunction Modules Opens TwoAffineOpenCover TwoAffineOpenCover.specMap Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial"
namespace TwoAffineOpenCover
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "sectionsOf specMap pullback isAffineOpen_U0 isAffineOpen_inf U1 U0 isAffineOpen_U1"
namespace SectionsBCDatum
r2nos_namespace_dual
w03_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) (M : X.Modules)
variable (A : Type u) [CommRing A] [Algebra R A]

theorem unit_res {U U' : X.Opens} (h : U' ≤ U)
    (h' : (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ U' ≤ (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ U)
    (m : Γ(M, U)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst c (specMap R A))).unit.app M).app U'
        (M.presheaf.map (homOfLE h).op m)
      = ((Scheme.Modules.pullback (Limits.pullback.fst c (specMap R A))).obj M).presheaf.map (homOfLE h').op
          (show Γ((Scheme.Modules.pullback (Limits.pullback.fst c (specMap R A))).obj M,
              (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ U) from
            ((Scheme.Modules.pullbackPushforwardAdjunction (Limits.pullback.fst c (specMap R A))).unit.app M).app U m) := by
  have hn := ((Scheme.Modules.pullbackPushforwardAdjunction
    (Limits.pullback.fst c (specMap R A))).unit.app M).mapPresheaf.naturality (homOfLE h).op
  have hx := ConcreteCategory.congr_hom hn m
  refine hx.trans ?_
  have : ((TopologicalSpace.Opens.map (Limits.pullback.fst c (specMap R A)).base).map (homOfLE h)) = homOfLE h' :=
    Subsingleton.elim _ _
  show (((Scheme.Modules.pullback (Limits.pullback.fst c (specMap R A))).obj M).presheaf.map
    ((TopologicalSpace.Opens.map (Limits.pullback.fst c (specMap R A)).base).map (homOfLE h)).op) _ = _
  rw [this]
  rfl

theorem tmul_eq_smul_one_tmul {N : Type u} [AddCommGroup N] [Module R N] (a : A) (n : N) :
    a ⊗ₜ[R] n = a • ((1 : A) ⊗ₜ[R] n) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.SectionsBCDatum

open AlgebraicGeometry.Scheme.TwoAffineOpenCover.SectionsBCDatum in
r2nos_open_dual "AlgebraicGeometry.Scheme.TwoAffineOpenCover.SectionsBCDatum" in
theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (A : Type u) [CommRing A] [Algebra R A] :
    ∃ (e0 : A ⊗[R] (𝒱.sectionsOf c M).M0 ≃ₗ[A]
          ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M0)
      (e1 : A ⊗[R] (𝒱.sectionsOf c M).M1 ≃ₗ[A]
          ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M1)
      (e01 : A ⊗[R] (𝒱.sectionsOf c M).M01 ≃ₗ[A]
          ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).M01),
      (∀ x, e01 (((𝒱.sectionsOf c M).r0.baseChange A) x) =
        ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).r0
            (e0 x)) ∧
      (∀ x, e01 (((𝒱.sectionsOf c M).r1.baseChange A) x) =
        ((𝒱.pullback c A).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).r1
            (e1 x)) ∧
      (∀ m : (𝒱.sectionsOf c M).M0, e0 ((1 : A) ⊗ₜ[R] m) =
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app 𝒱.U0).hom m) ∧
      (∀ m : (𝒱.sectionsOf c M).M1, e1 ((1 : A) ⊗ₜ[R] m) =
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app 𝒱.U1).hom m) ∧
      (∀ m : (𝒱.sectionsOf c M).M01, e01 ((1 : A) ⊗ₜ[R] m) =
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app (𝒱.U0 ⊓ 𝒱.U1)).hom m) := by
  obtain ⟨e0, he0⟩ := AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial
    c M htriv 𝒱.U0 𝒱.isAffineOpen_U0 A
  obtain ⟨e1, he1⟩ := AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial
    c M htriv 𝒱.U1 𝒱.isAffineOpen_U1 A
  obtain ⟨e01, he01⟩ := AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial
    c M htriv (𝒱.U0 ⊓ 𝒱.U1) 𝒱.isAffineOpen_inf A
  refine ⟨e0, e1, e01, ?_, ?_, he0, he1, he01⟩
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a m =>
      rw [LinearMap.baseChange_tmul, tmul_eq_smul_one_tmul (R := R) A a, tmul_eq_smul_one_tmul (R := R) A a m,
        map_smul, map_smul, map_smul]
      congr 1
      erw [he0, he01]
      exact unit_res c M A inf_le_left _ m
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a m =>
      rw [LinearMap.baseChange_tmul, tmul_eq_smul_one_tmul (R := R) A a, tmul_eq_smul_one_tmul (R := R) A a m,
        map_smul, map_smul, map_smul]
      congr 1
      erw [he1, he01]
      exact unit_res c M A inf_le_right _ m
end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_baseChange_equiv_of_locallyTrivial
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
