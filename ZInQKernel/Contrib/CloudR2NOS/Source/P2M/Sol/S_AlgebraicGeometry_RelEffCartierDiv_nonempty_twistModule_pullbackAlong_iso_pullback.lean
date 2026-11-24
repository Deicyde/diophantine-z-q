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
  Source file    : P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_nonempty_twistModule_pullbackAlong_iso_pullback.lean
  Source sha256  : 986abe1a0c1d54e3976ace448b96428d61d5b540b57b19876e4197e41473d55b
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 16 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_nonempty_twistModule_pullbackAlong_iso_pullback
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_nonempty_twistModule_pullbackAlong_iso_pullback.AlgebraicGeometry NeronModelInfra"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "SmoothOfRelativeDimension Scheme.Modules.pullback Scheme.Hom Spec Scheme Smooth Scheme.IdealSheafData.comap_top IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules Scheme.IdealSheafData RelEffCartierDiv.twistModule_def Scheme.Modules.rigidifyMapIso RelPicard.sectionIdeal Scheme.Modules.IsInvertible RelPicard.baseChangeSnd RelPicard.rigSection RelPicard.rigSection_baseChangeSnd RelEffCartierDiv RelEffCartierDiv.I RelEffCartierDiv.ofPoint Scheme.IdealSheafData.IsInvertible Scheme.Modules.pullbackTensorObjIso Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso RelEffCartierDiv.isInvertible_I RelEffCartierDiv.pullbackAlong_ofPoint Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.IdealSheafData.comap_mul Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso"
w03_open "AlgebraicGeometry"

theorem lbT_comap_pow {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ) :
    (I ^ n).comap f = (I.comap f) ^ n := by
  induction n with
  | zero => simp [Scheme.IdealSheafData.comap_top]
  | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

variable {R : Type u} [CommRing R] {C : Scheme.{u}}

theorem lbT_sectionIdeal_comap (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) :
    (RelPicard.sectionIdeal c ε t).comap (RelPicard.baseChangeSnd c ψ) =
      RelPicard.sectionIdeal c ε t' := by

  have hpt : (t ≫ ε.1) ≫ c = t := by rw [Category.assoc, ε.2, Category.comp_id]
  have hpt'' : (t' ≫ ε.1) ≫ c = t' := by rw [Category.assoc, ε.2, Category.comp_id]
  have hpt' : ψ.1 ≫ t ≫ ε.1 = t' ≫ ε.1 := by rw [← Category.assoc, ψ.2]
  have key := congrArg RelEffCartierDiv.I
    (RelEffCartierDiv.pullbackAlong_ofPoint c (t ≫ ε.1) hpt ψ.1 ψ.2)

  have e₁ : RelPicard.sectionIdeal c ε t = (RelEffCartierDiv.ofPoint c (t ≫ ε.1) hpt).I := rfl
  have e₂ : RelPicard.sectionIdeal c ε t' = (RelEffCartierDiv.ofPoint c (t' ≫ ε.1) hpt'').I := rfl
  have e₃ : (RelEffCartierDiv.ofPoint c (t ≫ ε.1) hpt).I.comap (RelPicard.baseChangeSnd c ψ) =
      ((RelEffCartierDiv.ofPoint c (t ≫ ε.1) hpt).pullbackAlong ψ.1 ψ.2).I := rfl
  rw [e₁, e₂, e₃, key]
  simp only [hpt']

end AlgebraicGeometry

variable {R : Type u} [CommRing R] {C : Scheme.{u}}

theorem solution (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) {r : ℕ} {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ψ : SchemeHomOver t' t) (D : RelEffCartierDiv c r t) :
    Nonempty ((D.pullbackAlong ψ.1 ψ.2).twistModule c ε ≅
      (Scheme.Modules.pullback (RelPicard.baseChangeSnd c ψ)).obj (D.twistModule c ε)) := by

  let Ψ := RelPicard.baseChangeSnd c ψ
  let σ := RelPicard.rigSection c t ε
  let σ' := RelPicard.rigSection c t' ε
  let J := RelPicard.sectionIdeal c ε t
  let J' := RelPicard.sectionIdeal c ε t'
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c t') :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance

  have hσ : σ' ≫ Ψ = ψ.1 ≫ σ := RelPicard.rigSection_baseChangeSnd c ε ψ
  have hq : Ψ ≫ pullback.snd c t = pullback.snd c t' ≫ ψ.1 := by
    simp only [Ψ, RelPicard.baseChangeSnd, pullback.map, pullback.lift_snd]

  have hσq : σ ≫ pullback.snd c t = 𝟙 T := by
    simp only [σ, RelPicard.rigSection, pullback.lift_snd]
  have hσq' : σ' ≫ pullback.snd c t' = 𝟙 T' := by
    simp only [σ', RelPicard.rigSection, pullback.lift_snd]
  have hJ : J.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id σ hσq
  have hJ' : J'.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id σ' hσq'
  have hJr : (J ^ r).IsInvertible := hJ.pow r
  have hD : D.I.IsInvertible := RelEffCartierDiv.isInvertible_I D
  have hD' : (D.pullbackAlong ψ.1 ψ.2).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I (D.pullbackAlong ψ.1 ψ.2)
  have hL : Scheme.Modules.IsInvertible (D.lineBundle ⊗ ((J ^ r).module)) :=
    hD.isInvertible_invModule.tensor hJr.isInvertible_module

  obtain ⟨e₁⟩ := Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso
    (σ := σ) (q := pullback.snd c t) (σ' := σ') (q' := pullback.snd c t') ψ.1 Ψ hσ hq hL

  have hcomapD : (D.pullbackAlong ψ.1 ψ.2).I = D.I.comap Ψ := rfl
  obtain ⟨e₂⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Ψ hD
    (hcomapD ▸ hD')

  have hcomapJ : (J ^ r).comap Ψ = J' ^ r := by
    rw [lbT_comap_pow]
    exact congrArg (· ^ r) (lbT_sectionIdeal_comap c ε ψ)
  have hJrc : ((J ^ r).comap Ψ).IsInvertible := hcomapJ ▸ hJ'.pow r
  haveI := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Ψ hJr hJrc
  let e₃ : (Scheme.Modules.pullback Ψ).obj ((J ^ r).module) ≅ (J' ^ r).module :=
    asIso ((J ^ r).pullbackModuleComparison Ψ) ≪≫ eqToIso (by rw [hcomapJ])

  let eL : (Scheme.Modules.pullback Ψ).obj (D.lineBundle ⊗ (J ^ r).module) ≅
      (D.pullbackAlong ψ.1 ψ.2).lineBundle ⊗ (J' ^ r).module :=
    Scheme.Modules.pullbackTensorObjIso Ψ _ _ ≪≫ (e₂ ⊗ᵢ e₃)
  refine ⟨?_⟩
  rw [RelEffCartierDiv.twistModule_def, RelEffCartierDiv.twistModule_def]
  exact (Scheme.Modules.rigidifyMapIso σ' (pullback.snd c t') eL).symm ≪≫ e₁.symm
end S_AlgebraicGeometry_RelEffCartierDiv_nonempty_twistModule_pullbackAlong_iso_pullback
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
