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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq.lean
  Source sha256  : caec7579c834178fb74ca7d8624647a15ca33266020e7130f29552887f5327cd
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 3200000 in`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 9 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_tensorHom
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq
r2nos_namespace_dual
r2nos_erase_attr "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
r2nos_erase_attr "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

universe u

set_option autoImplicit false
section translate_product
w03_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"
open scoped CategoryTheory.MonObj
r2nos_open_scoped_dual "CategoryTheory.MonObj"

namespace TPSol
r2nos_namespace_dual

variable {k : Type u} [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk t)]

noncomputable abbrev T (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) : X ⟶ X :=
  (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ x)).left

set_option pp.explicit true in
theorem T_inv_mul (y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) : T t (y⁻¹ * y) = 𝟙 X := by

  have h1 : (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y⁻¹)) ≫
      (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y)) = 𝟙 (Over.mk t) := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, CartesianMonoidalCategory.comp_toUnit,
      mul_assoc, GrpObj.comp_inv, inv_mul_cancel, mul_one]
  have h2 : (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y⁻¹)) ≫
      (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y)) =
      𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (y⁻¹ * y)) := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, CartesianMonoidalCategory.comp_toUnit,
      mul_assoc]
    congr 1
    exact (MonObj.comp_mul (CartesianMonoidalCategory.toUnit (Over.mk t)) y⁻¹ y).symm
  exact congrArg CommaMorphism.left (h2.symm.trans h1)

theorem support_zeroSchemeIdeal_pullbackSection {X' : Scheme.{u}} (F : X' ⟶ X) {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M) :
    ((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection F s)).support : Set X') =
      F.base ⁻¹' ((Scheme.Modules.zeroSchemeIdeal s).support : Set X) := by
  rw [← hM.comap_zeroSchemeIdeal F s, Scheme.IdealSheafData.support_comap]
  rfl

end TPSol

open TPSol in
r2nos_open_dual "TPSol" in
theorem solution
    (k : Type u) [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hsq : ∀ x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
      Nonempty (
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ x)).left).obj L ⊗
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y)).left).obj L ≅
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (x * y))).left).obj L ⊗
        L))
    (θ : 𝟙_ X.Modules ⟶ L)
    (a b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) :
    ∃ s : 𝟙_ X.Modules ⟶ L.tensorPow 3,
      ((Scheme.Modules.zeroSchemeIdeal s).support : Set X) =
        (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ a)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) ∪
          (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ b)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) ∪
          (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (a * b)⁻¹)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) := by
  classical

  let c : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t := (a * b)⁻¹
  let Lp : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) → X.Modules := fun x =>
    (Scheme.Modules.pullback (T t x)).obj L
  have hLp : ∀ x, Scheme.Modules.IsInvertible (Lp x) := fun x => hL.pullback _
  let θp : ∀ x, 𝟙_ X.Modules ⟶ Lp x := fun x => Scheme.Modules.pullbackSection (T t x) θ

  let sab : 𝟙_ X.Modules ⟶ Lp a ⊗ Lp b := (λ_ (𝟙_ X.Modules)).inv ≫ (θp a ⊗ₘ θp b)
  let s₀ : 𝟙_ X.Modules ⟶ Lp c ⊗ (Lp a ⊗ Lp b) := (λ_ (𝟙_ X.Modules)).inv ≫ (θp c ⊗ₘ sab)

  have hT1 : T t (c * (a * b)) = 𝟙 X := T_inv_mul t (a * b)
  have e1 : Lp (c * (a * b)) ≅ L :=
    (Scheme.Modules.pullbackCongr hT1).app L ≪≫ (Scheme.Modules.pullbackId X).app L
  have Φ₁ : Lp c ⊗ (Lp a ⊗ Lp b) ≅ Lp c ⊗ (Lp (a * b) ⊗ L) := whiskerLeftIso (Lp c) (hsq a b).some
  have Φ₂ : Lp c ⊗ (Lp (a * b) ⊗ L) ≅ (Lp c ⊗ Lp (a * b)) ⊗ L := (α_ (Lp c) (Lp (a * b)) L).symm
  have Φ₃ : (Lp c ⊗ Lp (a * b)) ⊗ L ≅ (Lp (c * (a * b)) ⊗ L) ⊗ L := whiskerRightIso (hsq c (a * b)).some L
  have Φ₄ : (Lp (c * (a * b)) ⊗ L) ⊗ L ≅ ((𝟙_ X.Modules ⊗ L) ⊗ L) ⊗ L :=
    whiskerRightIso (whiskerRightIso (e1 ≪≫ (λ_ L).symm) L) L
  have Φ : Lp c ⊗ (Lp a ⊗ Lp b) ≅ L.tensorPow 3 := Φ₁ ≪≫ Φ₂ ≪≫ Φ₃ ≪≫ Φ₄
  refine ⟨s₀ ≫ Φ.hom, ?_⟩
  rw [Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso]

  have hZ : Scheme.Modules.zeroSchemeIdeal s₀ =
      Scheme.Modules.zeroSchemeIdeal (θp c) *
        (Scheme.Modules.zeroSchemeIdeal (θp a) * Scheme.Modules.zeroSchemeIdeal (θp b)) := by
    rw [Scheme.Modules.IsInvertible.zeroSchemeIdeal_tensorHom (hLp c) ((hLp a).tensor (hLp b)),
      Scheme.Modules.IsInvertible.zeroSchemeIdeal_tensorHom (hLp a) (hLp b)]
  rw [hZ, Scheme.IdealSheafData.support_mul, Scheme.IdealSheafData.support_mul]
  simp only [TopologicalSpace.Closeds.coe_sup]
  rw [support_zeroSchemeIdeal_pullbackSection (T t c) hL θ, support_zeroSchemeIdeal_pullbackSection (T t a) hL θ,
    support_zeroSchemeIdeal_pullbackSection (T t b) hL θ]
  exact Set.union_comm _ _

end translate_product
end S_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
