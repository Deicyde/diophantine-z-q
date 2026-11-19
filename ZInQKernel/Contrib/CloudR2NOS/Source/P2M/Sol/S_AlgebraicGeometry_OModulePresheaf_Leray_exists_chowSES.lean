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
  Source file    : P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_exists_chowSES.lean
  Source sha256  : 45ecbe634fdd47598ebf931a961c0a19280590fc97d5162e355579e701ddd067
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 11 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 7 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
  * 2 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 6400000`; `set_option synthInstance.maxHeartbeats 1600000`; `set_option linter.unusedSectionVars false`; `set_option linter.unusedSimpArgs false`; `set_option linter.unusedVariables false`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 9 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_exists_hom_relHPresheaf_zero
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isCoherent_coker
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_coker
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_isCoherent_relHPresheaf_chow
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_chowSES
r2nos_namespace_dual
r2nos_erase_attr "instance" "ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
r2nos_erase_attr "simp" "ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"

set_option autoImplicit false

noncomputable section

universe u

w03_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_chowSES.AlgebraicGeometry TopologicalSpace Opposite CategoryTheory.Limits"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.Hom.map_appLE map_injective_of_isIntegral IsProper Scheme.Hom isPullback_morphismRestrict Spec IsIntegral Scheme image_morphismRestrict_preimage Scheme.Opens Scheme.Hom.appLE_map Scheme.Opens.ι_image_top morphismRestrict_app' Scheme.ΓSpecIso ProjSpace.stdCoverPullback ChowDatumProj OModulePresheaf OModulePresheaf.unit OModulePresheaf.Leray.relHPresheaf OModulePresheaf.SES"
namespace OModulePresheaf
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf" "IsCoherent IsQuasicoherent SupportedIn unit res module obj Leray.relHPresheaf Hom SES zero coker imCokerSES isCoherent_coker isQuasicoherent_coker"
w03_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

section General

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}

namespace Hom
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf.Hom" "naturality_apply comp app app_smul naturality"
end Hom
namespace Hom
r2nos_namespace_dual
r2nos_open_scoped "AlgebraicGeometry.OModulePresheaf.Hom" in

private def _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.OModulePresheaf.Hom.symmOfBijective {F G : OModulePresheaf π} (φ : Hom F G)
    (hφ : ∀ U : V.Opens, Function.Bijective (φ.app U)) : Hom G F where
  app U := ((LinearEquiv.ofBijective (φ.app U) (hφ U)).symm : G.obj U →ₗ[R] F.obj U)
  app_smul U a y := by
    apply (hφ U).1
    show φ.app U ((LinearEquiv.ofBijective (φ.app U) (hφ U)).symm (a • y))
      = φ.app U (a • (LinearEquiv.ofBijective (φ.app U) (hφ U)).symm y)
    rw [φ.app_smul]
    erw [(LinearEquiv.ofBijective (φ.app U) (hφ U)).apply_symm_apply,
      (LinearEquiv.ofBijective (φ.app U) (hφ U)).apply_symm_apply]
  naturality {U U'} h := by
    refine LinearMap.ext fun y => (hφ U).1 ?_
    show φ.app U ((LinearEquiv.ofBijective (φ.app U) (hφ U)).symm (G.res h y))
      = φ.app U (F.res h ((LinearEquiv.ofBijective (φ.app U') (hφ U')).symm y))
    rw [φ.naturality_apply]
    erw [(LinearEquiv.ofBijective (φ.app U) (hφ U)).apply_symm_apply,
      (LinearEquiv.ofBijective (φ.app U') (hφ U')).apply_symm_apply]

end Hom
w03_export "AlgebraicGeometry.OModulePresheaf" "Hom.symmOfBijective"
namespace Hom
r2nos_namespace_dual
r2nos_open_scoped "AlgebraicGeometry.OModulePresheaf.Hom" in
private theorem _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.OModulePresheaf.Hom.symmOfBijective_bijective {F G : OModulePresheaf π} (φ : Hom F G)
    (hφ : ∀ U : V.Opens, Function.Bijective (φ.app U)) (U : V.Opens) :
    Function.Bijective ((φ.symmOfBijective hφ).app U) :=
  (LinearEquiv.ofBijective (φ.app U) (hφ U)).symm.bijective

end Hom
w03_export "AlgebraicGeometry.OModulePresheaf" "Hom.symmOfBijective_bijective"
variable (π) in

theorem isQuasicoherent_unit : (unit π).IsQuasicoherent := by
  intro U f
  haveI := U.2.isLocalization_basicOpen f
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  ·
    have hcore : ∀ x' : Γ(V, V.basicOpen f), ∃ (n : ℕ) (y : Γ(V, U.1)),
        (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom y
          = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n) * x' := fun x' => by
      obtain ⟨⟨y, _, n, rfl⟩, hxy⟩ :=
        IsLocalization.surj (S := Γ(V, V.basicOpen f)) (.powers f) x'
      exact ⟨n, y, hxy.symm.trans (mul_comm _ _)⟩
    exact hcore x
  · have hy' : algebraMap Γ(V, U.1) Γ(V, V.basicOpen f) y = 0 := hy
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (.powers f) _ _).mp hy'
    exact ⟨n, hn⟩

end General

namespace Leray
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf.Leray" "pullOpen relHPresheaf exists_hom_relHPresheaf_zero isCoherent_relHPresheaf_chow isQuasicoherent_relHPresheaf_chow"
w03_open "AlgebraicGeometry.OModulePresheaf.Leray"

section UnitToPullOpen

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R))

def unitToPullOpen : Hom (unit πZ) (pullOpen p πZ (⊤ : V'.Opens)) where
  app U :=
    { toFun := fun s => (p.appLE U ((⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U) inf_le_right).hom s
      map_add' := fun s₁ s₂ => map_add _ s₁ s₂
      map_smul' := fun r s => by

        have hcore : ∀ s' : Γ(Z, U),
            (p.appLE U ((⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U) inf_le_right).hom
                ((Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
                  ((πZ.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) * s')
              = (V'.presheaf.map (homOfLE le_top).op).hom
                  (((p ≫ πZ).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
                * (p.appLE U _ inf_le_right).hom s' := fun s' => by
          rw [map_mul, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]; rfl
        exact hcore s }
  app_smul U a s := by
    have hcore : ∀ s' : Γ(Z, U),
        (p.appLE U ((⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U) inf_le_right).hom (a * s')
          = (p.appLE U _ inf_le_right).hom a * (p.appLE U _ inf_le_right).hom s' :=
      fun s' => map_mul _ a s'
    exact hcore s
  naturality {U U'} h := by
    refine LinearMap.ext fun s => ?_
    show (p.appLE U ((⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U) inf_le_right).hom
        ((Z.presheaf.map (homOfLE h).op).hom s)
      = (V'.presheaf.map
          (homOfLE (inf_le_inf_left _ ((Opens.map p.base).monotone h))).op).hom
          ((p.appLE U' ((⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U') inf_le_right).hom s)
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
      Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]

theorem unitToPullOpen_app (U : Z.Opens) (s : Γ(Z, U)) :
    (unitToPullOpen p πZ).app U s
      = (p.appLE U ((⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U) inf_le_right).hom s := rfl

end UnitToPullOpen

section Chow

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {Z : Scheme.{u}}
variable (πZ : Z ⟶ Spec (CommRingCat.of R)) [IsIntegral Z]
variable (D : ChowDatumProj πZ)

theorem chow_restrict_isIso {W : Z.Opens} (hWU : W ≤ D.U) :
    IsIso (D.p ∣_ W) := by
  have heq : (isPullback_morphismRestrict D.p W).flip.isoPullback.hom ≫
      (Limits.pullback.congrHom rfl (Z.homOfLE_ι hWU).symm).hom ≫
      (Limits.pullbackLeftPullbackSndIso D.p D.U.ι (Z.homOfLE hWU)).inv ≫
      Limits.pullback.snd _ _ = D.p ∣_ W := by
    simp only [Limits.pullbackLeftPullbackSndIso_inv_snd_snd, Limits.pullback.congrHom_hom,
      Category.assoc]

    erw [Limits.pullback.lift_snd]
    rw [Category.comp_id, (isPullback_morphismRestrict D.p W).flip.isoPullback_hom_snd]
  exact heq ▸ inferInstance

theorem chow_appLE_bijective_of_le_U {W : Z.Opens} (hWU : W ≤ D.U) :
    Function.Bijective
      (D.p.appLE W ((⊤ : D.V'.Opens) ⊓ (Opens.map D.p.base).obj W) inf_le_right).hom := by
  haveI := chow_restrict_isIso πZ D hWU
  haveI happiso : IsIso ((D.p ∣_ W).app ⊤) := inferInstance
  haveI : IsIso (D.p.appLE W ((⊤ : D.V'.Opens) ⊓ (Opens.map D.p.base).obj W) inf_le_right) := by
    refine (D.p.appLE_congr (image_morphismRestrict_preimage D.p W ⊤).le
        (Scheme.Opens.ι_image_top W)
        (show (D.p ⁻¹ᵁ W).ι ''ᵁ ((D.p ∣_ W) ⁻¹ᵁ ⊤)
            = (⊤ : D.V'.Opens) ⊓ (Opens.map D.p.base).obj W from by
          rw [Opens.map_top, Scheme.Opens.ι_image_top]; exact (top_inf_eq _).symm)
        (fun g => IsIso g)).mp ?_
    exact morphismRestrict_app' D.p W ⊤ ▸ happiso
  exact ConcreteCategory.bijective_of_isIso _

theorem unitToPullOpen_injective_chow (U : Z.Opens) :
    Function.Injective ((unitToPullOpen D.p πZ).app U) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  have h0 : (D.p.appLE U ((⊤ : D.V'.Opens) ⊓ (Opens.map D.p.base).obj U) inf_le_right).hom s
      = 0 := hs

  have h0W : (D.p.appLE (U ⊓ D.U)
      ((⊤ : D.V'.Opens) ⊓ (Opens.map D.p.base).obj (U ⊓ D.U)) inf_le_right).hom
      ((Z.presheaf.map (homOfLE inf_le_left).op).hom s) = 0 := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
      ← Scheme.Hom.appLE_map _ inf_le_right (homOfLE (inf_le_inf_left _
        ((Opens.map D.p.base).monotone (inf_le_left : U ⊓ D.U ≤ U)))).op,
      CommRingCat.comp_apply, h0, map_zero]
  have hsW : (Z.presheaf.map (homOfLE (inf_le_left : U ⊓ D.U ≤ U)).op).hom s = 0 :=
    (chow_appLE_bijective_of_le_U πZ D (inf_le_right : U ⊓ D.U ≤ D.U)).1
      (h0W.trans (map_zero _).symm)

  rcases (U : Set Z).eq_empty_or_nonempty with hU | hU
  · obtain rfl : U = ⊥ := SetLike.ext' hU
    exact @Subsingleton.elim _ (inferInstance : Subsingleton Γ(Z, (⊥ : Z.Opens))) s 0
  · haveI : Nonempty (U ⊓ D.U : Z.Opens) :=
      (nonempty_preirreducible_inter U.isOpen D.U.isOpen hU D.hU_dense.nonempty).to_subtype
    exact map_injective_of_isIntegral Z (homOfLE inf_le_left) (hsW.trans (map_zero _).symm)

theorem exists_chowSES' [IsNoetherianRing R] [IsProper πZ] :
    ∃ (Q : OModulePresheaf πZ) (S : OModulePresheaf.SES (OModulePresheaf.unit πZ)
          (relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) 0) Q),
      Q.IsCoherent ∧ Q.IsQuasicoherent ∧ Q.SupportedIn ⟨(D.U : Set Z)ᶜ, D.U.isOpen.isClosed_compl⟩ := by
  set K' := ProjSpace.stdCoverPullback D.ιN

  obtain ⟨φ, hφ, -⟩ := exists_hom_relHPresheaf_zero D.p πZ K'
  let ψ : Hom (pullOpen D.p πZ (⊤ : D.V'.Opens)) (relHPresheaf D.p πZ K' 0) := φ.symmOfBijective hφ
  have hψ : ∀ U, Function.Bijective (ψ.app U) := φ.symmOfBijective_bijective hφ

  let χ : Hom (unit πZ) (relHPresheaf D.p πZ K' 0) := ψ.comp (unitToPullOpen D.p πZ)
  have hχinj : ∀ U, Function.Injective (χ.app U) := fun U =>
    (hψ U).1.comp (unitToPullOpen_injective_chow πZ D U)
  refine ⟨coker χ,
    { inc := χ
      proj := (imCokerSES χ).proj
      injective := hχinj
      surjective := (imCokerSES χ).surjective
      exact := fun U => (Submodule.ker_mkQ (LinearMap.range (χ.app U))).symm },
    isCoherent_coker χ (isCoherent_relHPresheaf_chow πZ D 0),
    isQuasicoherent_coker χ (isQuasicoherent_relHPresheaf_chow πZ D 0) (isQuasicoherent_unit πZ),
    fun W hW => ?_⟩

  have hWU : (W : Z.Opens) ≤ D.U := fun x hx =>
    not_not.mp fun hc => (Set.ext_iff.mp hW x).mp ⟨hx, hc⟩
  refine Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr ?_)
  exact (hψ W.1).2.comp (chow_appLE_bijective_of_le_U πZ D hWU).2

end Chow

end Leray

end AlgebraicGeometry.OModulePresheaf

open CategoryTheory _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_chowSES.AlgebraicGeometry in
r2nos_open_dual "CategoryTheory _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_exists_chowSES.AlgebraicGeometry" in
theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R]
    {Z : Scheme.{u}} (πZ : Z ⟶ Spec (.of R)) [IsProper πZ] [IsIntegral Z] (D : ChowDatumProj πZ) :
    ∃ (Q : OModulePresheaf πZ) (S : OModulePresheaf.SES (OModulePresheaf.unit πZ)
          (OModulePresheaf.Leray.relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) 0) Q),
      Q.IsCoherent ∧ Q.IsQuasicoherent ∧ Q.SupportedIn ⟨(D.U : Set Z)ᶜ, D.U.isOpen.isClosed_compl⟩ :=
  AlgebraicGeometry.OModulePresheaf.Leray.exists_chowSES' πZ D

end
end S_AlgebraicGeometry_OModulePresheaf_Leray_exists_chowSES
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
