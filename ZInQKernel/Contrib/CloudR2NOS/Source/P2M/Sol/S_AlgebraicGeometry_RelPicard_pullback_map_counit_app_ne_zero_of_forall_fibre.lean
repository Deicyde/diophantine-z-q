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
  Source file    : P2M/Sol/S_AlgebraicGeometry_RelPicard_pullback_map_counit_app_ne_zero_of_forall_fibre.lean
  Source sha256  : eb316a1c78c5c62be3b3a0fcc9eecbcd48ed282c22548142ba756626caef19ea
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 7 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 7 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `attribute [-simp]`/`[-instance]` guard line(s) -> `r2nos_erase_attr` (unknown or already-erased names warn instead of aborting; these lines only remove simp lemmas/instances).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 16 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelPicard_isIso_baseChangeHom_pushforward_of_forall_fibre
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_FiniteMapData_exists_baseChange
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_RelPicard_pullback_map_counit_app_ne_zero_of_forall_fibre
r2nos_namespace_dual
r2nos_erase_attr "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply"

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_pullback_map_counit_app_ne_zero_of_forall_fibre.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_pullback_map_counit_app_ne_zero_of_forall_fibre.AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve"

noncomputable section

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Spec.map_preimage Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension Scheme.Modules.pushforward IsProper Scheme.Modules.pullback Scheme.Modules.Hom LocallyOfFiniteType Spec Spec.map Scheme Scheme.Modules.Hom.app Spec.preimage Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules Scheme.Modules.IsInvertible SmoothProperCurve.FiniteMapData mapOnProdOver isPullback_mapOnProdOver RelPicard.BaseChange.baseChangeSnd_snd' Scheme.Modules.pullbackTwoSquare Scheme.Modules.baseChangeHom Scheme.Modules.baseChangeHom_counit RelPicard.isIso_baseChangeHom_pushforward_of_forall_fibre RelPicard.exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback"
namespace RelPicard
r2nos_namespace_dual
w03_export "AlgebraicGeometry.RelPicard" "baseChangeSnd fibreAt fibreModule BaseChange.baseChangeSnd_snd' isIso_baseChangeHom_pushforward_of_forall_fibre exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback"
namespace NZCounitSol
r2nos_namespace_dual
w03_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {Y S : Scheme.{u}} (π : Y ⟶ S)

theorem app_top_eq_zero_of_counit_eq_zero (N : Y.Modules)
    (h : (Scheme.Modules.pullbackPushforwardAdjunction π).counit.app N = 0) (m : Γ(N, ⊤)) : m = 0 := by
  have tri := (Scheme.Modules.pullbackPushforwardAdjunction π).right_triangle_components N

  have e1 := congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤ (show Γ((Scheme.Modules.pushforward π).obj N, ⊤) from m)) tri

  change (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction π).counit.app N) (π ⁻¹ᵁ ⊤))
      ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app _) ⊤)
        (show Γ((Scheme.Modules.pushforward π).obj N, ⊤) from m))
    = (show Γ((Scheme.Modules.pushforward π).obj N, ⊤) from m) at e1
  have e3 := congrArg (fun φ => Scheme.Modules.Hom.app φ (π ⁻¹ᵁ ⊤)
    ((Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app _) ⊤)
      (show Γ((Scheme.Modules.pushforward π).obj N, ⊤) from m))) h

  simp only [Scheme.Modules.Hom.zero_app] at e3
  have e4 : (show Γ((Scheme.Modules.pushforward π).obj N, ⊤) from m) = 0 :=
    e1.symm.trans (e3.trans (by
      first
        | rfl
        | (rw [Scheme.Modules.Hom.zero_app]; rfl)
        | simp [Scheme.Modules.Hom.zero_app]
        | exact map_zero _))
  exact e4

end AlgebraicGeometry.RelPicard.NZCounitSol

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Spec.map_preimage Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension Scheme.Modules.pushforward IsProper Scheme.Modules.pullback Scheme.Modules.Hom LocallyOfFiniteType Spec Spec.map Scheme Scheme.Modules.Hom.app Spec.preimage Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules Scheme.Modules.IsInvertible SmoothProperCurve.FiniteMapData mapOnProdOver isPullback_mapOnProdOver RelPicard.BaseChange.baseChangeSnd_snd' Scheme.Modules.pullbackTwoSquare Scheme.Modules.baseChangeHom Scheme.Modules.baseChangeHom_counit RelPicard.isIso_baseChangeHom_pushforward_of_forall_fibre RelPicard.exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback"
namespace RelPicard
r2nos_namespace_dual
w03_export "AlgebraicGeometry.RelPicard" "baseChangeSnd fibreAt fibreModule BaseChange.baseChangeSnd_snd' isIso_baseChangeHom_pushforward_of_forall_fibre exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback"
namespace NZCounitSol
r2nos_namespace_dual
w03_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

theorem main
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 = 1)
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ T) :
    (Scheme.Modules.pullback (mapOnProdOver c x rfl)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd c t)).counit.app M) ≠ 0 := by
  intro h0

  haveI hbc := RelPicard.isIso_baseChangeHom_pushforward_of_forall_fibre R c ε h𝔉
    (⟨x, rfl⟩ : SchemeHomOver (x ≫ t) t) M hM 1 hfib

  have key := Scheme.Modules.baseChangeHom_counit (π := pullback.snd c t) (ψ := x) (π' := pullback.snd c (x ≫ t))
    (g' := baseChangeSnd c (⟨x, rfl⟩ : SchemeHomOver (x ≫ t) t))
    (RelPicard.BaseChange.baseChangeSnd_snd' (cc := c) (ψ := (⟨x, rfl⟩ : SchemeHomOver (x ≫ t) t))) M
  have h0' : (Scheme.Modules.pullback (baseChangeSnd c (⟨x, rfl⟩ : SchemeHomOver (x ≫ t) t))).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd c t)).counit.app M) = 0 := h0
  have key2 : (Scheme.Modules.pullback (pullback.snd c (x ≫ t))).map
        (Scheme.Modules.baseChangeHom
          (RelPicard.BaseChange.baseChangeSnd_snd' (cc := c) (ψ := (⟨x, rfl⟩ : SchemeHomOver (x ≫ t) t))) M) ≫
      (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd c (x ≫ t))).counit.app
        ((Scheme.Modules.pullback (baseChangeSnd c (⟨x, rfl⟩ : SchemeHomOver (x ≫ t) t))).obj M) = 0 := by
    refine key.trans ?_
    refine (congrArg (fun φ => (Scheme.Modules.pullbackTwoSquare
      (RelPicard.BaseChange.baseChangeSnd_snd' (cc := c) (ψ := (⟨x, rfl⟩ : SchemeHomOver (x ≫ t) t)))).natTrans.app
        ((Scheme.Modules.pushforward (pullback.snd c t)).obj M) ≫ φ) h0').trans ?_
    exact Limits.comp_zero
  have hcounit : (Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd c (x ≫ t))).counit.app
      ((Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M) = 0 := by
    have := (cancel_epi ((Scheme.Modules.pullback (pullback.snd c (x ≫ t))).map
      (Scheme.Modules.baseChangeHom
        (RelPicard.BaseChange.baseChangeSnd_snd' (cc := c) (ψ := (⟨x, rfl⟩ : SchemeHomOver (x ≫ t) t))) M))).mp
      (key2.trans (Limits.comp_zero).symm)
    exact this

  have hsec : ∀ m : Γ((Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M, ⊤), m = 0 :=
    app_top_eq_zero_of_counit_eq_zero (pullback.snd c (x ≫ t)) _ hcounit

  letI : Algebra R k := (Spec.preimage (x ≫ t)).hom.toAlgebra
  have hx : Spec.map (CommRingCat.ofHom (algebraMap R k)) = x ≫ t := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage (x ≫ t)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨𝔉, -⟩ := h𝔉 0
  obtain ⟨𝔉k, -, -, -, -⟩ := 𝔉.exists_baseChange k
  let 𝒱 : (pullback c (x ≫ t)).TwoAffineOpenCover := hx ▸ 𝔉k.twoAffineOpenCover

  obtain ⟨𝒲, ⟨e0⟩, -⟩ := RelPicard.exists_twoAffineOpenCover_fibre_linearEquiv_sectionsOf_of_isPullback c t M x
    (pullback.snd c (x ≫ t)) (mapOnProdOver c x rfl) (isPullback_mapOnProdOver c x rfl)
    ((Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M) (Iso.refl _) 𝒱
  obtain ⟨-, h1⟩ := hfib k x 𝒲
  have hrank : Module.finrank k (𝒱.sectionsOf (pullback.snd c (x ≫ t))
      ((Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M)).H0 = 1 := e0.finrank_eq.trans h1

  obtain ⟨eΓ, -⟩ := 𝒱.exists_linearEquiv_sectionsOf_H0 (pullback.snd c (x ≫ t))
    ((Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M)
  haveI : Nontrivial (𝒱.sectionsOf (pullback.snd c (x ≫ t))
      ((Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M)).H0 := Module.nontrivial_of_finrank_eq_succ hrank
  obtain ⟨a, b, hab⟩ := exists_pair_ne (𝒱.sectionsOf (pullback.snd c (x ≫ t))
      ((Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M)).H0
  apply hab
  rw [← eΓ.apply_symm_apply a, ← eΓ.apply_symm_apply b, hsec (eΓ.symm a), hsec (eΓ.symm b)]

end AlgebraicGeometry.RelPicard.NZCounitSol

end

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (M : (pullback c t).Modules) (hM : Scheme.Modules.IsInvertible M)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H0 = 1)
    {k : Type u} [Field k] (x : Spec (CommRingCat.of k) ⟶ T) :
    (Scheme.Modules.pullback (mapOnProdOver c x rfl)).map
      ((Scheme.Modules.pullbackPushforwardAdjunction (pullback.snd c t)).counit.app M) ≠ 0 :=
  AlgebraicGeometry.RelPicard.NZCounitSol.main R c ε h𝔉 t M hM hfib x
end S_AlgebraicGeometry_RelPicard_pullback_map_counit_app_ne_zero_of_forall_fibre
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
