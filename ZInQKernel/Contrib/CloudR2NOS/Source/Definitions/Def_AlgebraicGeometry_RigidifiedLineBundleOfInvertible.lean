/-
NOS-CORE PROBE STAGING COPY (NOS-core probe, lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : Definitions/Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible.lean
  Source sha256  : b039cf60aa56cc4a7b127881283fb7c1cdf805a448223595b20753b3ed08a83d
  Retrieved      : pinned upstream https://github.com/anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2, byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 9 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * BATCH-8 (lane C4): T10×1
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesRigidify
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual_tensor
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

universe u

open CategoryTheory
r2nos_open_dual "CategoryTheory"
open CategoryTheory.Limits
r2nos_open_dual "CategoryTheory.Limits"
open MonoidalCategory
r2nos_open_dual "MonoidalCategory"
open AlgebraicGeometry
r2nos_open_dual "AlgebraicGeometry"
open AlgebraicGeometry.RelPicard
r2nos_open_dual "AlgebraicGeometry.RelPicard"
open NeronModelInfra
r2nos_open_dual "NeronModelInfra"
open GoodReductionJacobian
r2nos_open_dual "GoodReductionJacobian"

noncomputable section

namespace AlgebraicGeometry
r2nos_namespace_dual

namespace Scheme.Modules
r2nos_namespace_dual

variable {V : Scheme.{u}}

def isoOfTensorIsoUnit (X Y Y' : V.Modules) (i : X ⊗ Y ≅ 𝟙_ _) (i' : X ⊗ Y' ≅ 𝟙_ _) : Y ≅ Y' :=
  (λ_ Y).symm ≪≫ (i'.symm ⊗ᵢ Iso.refl Y) ≪≫ ((β_ X Y') ⊗ᵢ Iso.refl Y) ≪≫ α_ Y' X Y ≪≫ (Iso.refl Y' ⊗ᵢ i) ≪≫ ρ_ Y'

def tensorTensorTensorComm (W X Y Z : V.Modules) : (W ⊗ X) ⊗ (Y ⊗ Z) ≅ (W ⊗ Y) ⊗ (X ⊗ Z) :=
  α_ _ _ _ ≪≫ (Iso.refl W ⊗ᵢ ((α_ _ _ _).symm ≪≫ (β_ X Y ⊗ᵢ Iso.refl Z) ≪≫ α_ _ _ _)) ≪≫ (α_ _ _ _).symm

theorem nonempty_dual_tensorUnit_iso (V : Scheme.{u}) : Nonempty (dual (𝟙_ V.Modules) ≅ 𝟙_ V.Modules) :=
  ⟨(λ_ _).symm ≪≫ (isInvertible_unit V).dual.2.some⟩

end Scheme.Modules

namespace RelPicard
r2nos_namespace_dual

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {T T' : Scheme.{u}}
  {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}

@[reassoc (attr := simp)]
theorem rigSection_snd (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (t : T ⟶ Spec (CommRingCat.of R)) :
    rigSection c t ε ≫ pullback.snd c t = 𝟙 T :=
  pullback.lift_snd _ _ _

@[reassoc]
theorem baseChangeSnd_snd (ψ : SchemeHomOver t' t) :
    baseChangeSnd c ψ ≫ pullback.snd c t = pullback.snd c t' ≫ ψ.1 :=
  pullback.lift_snd _ _ _

abbrev rigCorrection (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (t : T ⟶ Spec (CommRingCat.of R))
    (L : (Limits.pullback c t).Modules) : T.Modules :=
  Scheme.Modules.dual ((Scheme.Modules.pullback (rigSection c t ε)).obj L)

def rigSectionPullbackSndPullbackIso (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (t : T ⟶ Spec (CommRingCat.of R))
    (D : T.Modules) :
    (Scheme.Modules.pullback (rigSection c t ε)).obj ((Scheme.Modules.pullback (pullback.snd c t)).obj D) ≅ D :=
  (Scheme.Modules.pullbackComp _ _).app D ≪≫ (Scheme.Modules.pullbackCongr (rigSection_snd ε t)).app D ≪≫
    (Scheme.Modules.pullbackId _).app D

def RigidifiedLineBundle.ofInvertible (L : (Limits.pullback c t).Modules) (hL : Scheme.Modules.IsInvertible L) :
    RigidifiedLineBundle c ε t where
  L := Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t) L
  isInvertible := hL.tensor (((hL.pullback _).dual).1.pullback _)
  rigidified := ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫
    (Iso.refl _ ⊗ᵢ rigSectionPullbackSndPullbackIso ε t _) ≪≫ (hL.pullback _).dual.2.some⟩

@[simp] theorem RigidifiedLineBundle.ofInvertible_L (L : (Limits.pullback c t).Modules) (hL : Scheme.Modules.IsInvertible L) :
    (RigidifiedLineBundle.ofInvertible (ε := ε) L hL).L = Scheme.Modules.rigidify (rigSection c t ε) (pullback.snd c t) L := rfl

theorem RigidifiedLineBundle.ofInvertible_L_eq_tensor (L : (Limits.pullback c t).Modules) (hL : Scheme.Modules.IsInvertible L) :
    (RigidifiedLineBundle.ofInvertible (ε := ε) L hL).L =
      L ⊗ (Scheme.Modules.pullback (pullback.snd c t)).obj (rigCorrection ε t L) := rfl

namespace RigidifiedLineBundle
r2nos_namespace_dual

theorem nonempty_ofInvertible_iso_of_iso {L L' : (Limits.pullback c t).Modules} (hL : Scheme.Modules.IsInvertible L)
    (hL' : Scheme.Modules.IsInvertible L') (e : L ≅ L') :
    Nonempty ((ofInvertible (ε := ε) L hL).L ≅ (ofInvertible (ε := ε) L' hL').L) := by
  exact ⟨Scheme.Modules.rigidifyMapIso _ _ e⟩

theorem nonempty_ofInvertible_iso_of_rigidified (M : RigidifiedLineBundle c ε t) :
    Nonempty ((ofInvertible (ε := ε) M.L M.isInvertible).L ≅ M.L) := by
  let d := Scheme.Modules.dualMapIso M.rigidified.some
  obtain ⟨u⟩ := Scheme.Modules.nonempty_dual_tensorUnit_iso T
  exact ⟨(Iso.refl _ ⊗ᵢ ((Scheme.Modules.pullback _).mapIso (d ≪≫ u) ≪≫ Scheme.Modules.pullbackTensorUnitObjIso _)) ≪≫
    ρ_ M.L⟩

theorem nonempty_ofInvertible_tensor_iso {L L' : (Limits.pullback c t).Modules} (hL : Scheme.Modules.IsInvertible L)
    (hL' : Scheme.Modules.IsInvertible L') :
    Nonempty ((ofInvertible (ε := ε) (L ⊗ L') (hL.tensor hL')).L ≅
      ((ofInvertible (ε := ε) L hL).tensor (ofInvertible (ε := ε) L' hL')).L) := by
  have hεL := hL.pullback (rigSection c t ε)
  have hεL' := hL'.pullback (rigSection c t ε)

  let d₁ := Scheme.Modules.dualMapIso (Scheme.Modules.pullbackTensorObjIso (rigSection c t ε) L L')
  obtain ⟨d₂⟩ := hεL.dual_tensor hεL'
  refine ⟨(Iso.refl _ ⊗ᵢ ((Scheme.Modules.pullback _).mapIso (d₁ ≪≫ d₂) ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _)) ≪≫
    Scheme.Modules.tensorTensorTensorComm _ _ _ _⟩

theorem nonempty_ofInvertible_pullbackSnd_tensor_iso {N : T.Modules} (hN : Scheme.Modules.IsInvertible N)
    {L : (Limits.pullback c t).Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty ((ofInvertible (ε := ε) ((Scheme.Modules.pullback (pullback.snd c t)).obj N ⊗ L) ((hN.pullback _).tensor hL)).L ≅
      (ofInvertible (ε := ε) L hL).L) := by
  have hεL := hL.pullback (rigSection c t ε)

  let d₁ := Scheme.Modules.dualMapIso
    (Scheme.Modules.pullbackTensorObjIso (rigSection c t ε) _ L ≪≫ (rigSectionPullbackSndPullbackIso ε t N ⊗ᵢ Iso.refl _))
  obtain ⟨d₂⟩ := hN.dual_tensor hεL
  obtain ⟨p⟩ := hN.dual.2
  refine ⟨(Iso.refl _ ⊗ᵢ ((Scheme.Modules.pullback _).mapIso (d₁ ≪≫ d₂) ≪≫ Scheme.Modules.pullbackTensorObjIso _ _ _)) ≪≫
    Scheme.Modules.tensorTensorTensorComm _ _ _ _ ≪≫
    (((Scheme.Modules.pullbackTensorObjIso _ _ _).symm ≪≫ (Scheme.Modules.pullback _).mapIso p ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso _) ⊗ᵢ Iso.refl _) ≪≫ λ_ _⟩

theorem nonempty_ofInvertible_pullbackAlong_iso (ψ : SchemeHomOver t' t) {L : (Limits.pullback c t).Modules}
    (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (((ofInvertible (ε := ε) L hL).pullbackAlong ψ).L ≅
      (ofInvertible (ε := ε) ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj L) (hL.pullback _)).L) := by
  have hεL := hL.pullback (rigSection c t ε)

  obtain ⟨d₁⟩ := hεL.pullback_dual ψ.1
  let d₂ := Scheme.Modules.dualMapIso
    ((Scheme.Modules.pullbackComp ψ.1 (rigSection c t ε)).app L ≪≫
      (Scheme.Modules.pullbackCongr (rigSection_baseChangeSnd c ε ψ).symm).app L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app L).symm)
  refine ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (Iso.refl _ ⊗ᵢ ?_)⟩

  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr (baseChangeSnd_snd ψ)).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm ≪≫ (Scheme.Modules.pullback _).mapIso (d₁ ≪≫ d₂)

end RigidifiedLineBundle

end RelPicard

end AlgebraicGeometry

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
