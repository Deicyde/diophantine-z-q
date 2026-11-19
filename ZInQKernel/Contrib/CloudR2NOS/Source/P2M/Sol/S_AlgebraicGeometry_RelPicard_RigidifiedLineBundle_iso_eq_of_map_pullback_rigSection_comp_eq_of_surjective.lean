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
  Source file    : P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective.lean
  Source sha256  : 97906b19306e94ac4d322e18e8f61b4f859dc70194470203310d56b2d189c900
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 11 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 4 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective.AlgebraicGeometry Opposite"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Surjective Scheme.Modules.pullback Scheme.Hom Scheme.Modules.Hom Spec Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app Scheme.Hom.appTop Scheme.Hom.comp_appTop Scheme.Hom.naturality Scheme.Modules Scheme.Modules.IsInvertible Scheme.Modules.IsInvertible.existsUnique_app_eq_smul"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "ringCatSheaf Modules.pullback Hom.id_app Hom Γ Hom.app Modules.Hom Modules.Hom.id_app Modules.Hom.app Hom.appTop Hom.comp_appTop Hom.naturality Modules Opens Modules.map_smul PresheafOfModules Modules.IsInvertible Modules.IsInvertible.existsUnique_app_eq_smul"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pushforward pullback presheaf Hom mapPresheaf_app Hom.id_app Hom.app pullbackPushforwardAdjunction map_smul IsInvertible IsInvertible.existsUnique_app_eq_smul"
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X Y : Scheme.{u}}

noncomputable abbrev unitModule (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

namespace Hom
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules.Hom" "app_smul mapPresheaf id_app app"
end Hom
r2nos_open_scoped "AlgebraicGeometry.Scheme.Modules.Hom" in

lemma Hom.app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) (x : Γ(M, V)) :
    φ.app U (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app V x) := by
  have h := φ.mapPresheaf.naturality i.op
  simp only [mapPresheaf_app] at h
  have h' := ConcreteCategory.congr_hom h x
  simp only [ConcreteCategory.comp_apply] at h'
  exact h'

noncomputable abbrev resTop (s : Γ(X, ⊤)) (U : X.Opens) : Γ(X, U) :=
  X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s

@[scoped simp] lemma map_resTop (s : Γ(X, ⊤)) {U V : X.Opens} (i : U ⟶ V) :
    X.presheaf.map i.op (resTop s V) = resTop s U := by
  simp only [resTop, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

@[scoped simp] lemma resTop_top (s : Γ(X, ⊤)) : resTop s ⊤ = s := by
  simp [resTop]

lemma smul_res_comm (s : Γ(X, ⊤)) (M : X.Modules) (U : X.Opens) (r : Γ(X, U)) (m : Γ(M, U)) :
    resTop s U • r • m = r • resTop s U • m := by
  rw [smul_smul, smul_smul, mul_comm]

lemma map_resTop_smul (s : Γ(X, ⊤)) (M : X.Modules) {U V : X.Opens} (i : U ⟶ V) (x : Γ(M, V)) :
    M.presheaf.map i.op (resTop s V • x) = resTop s U • M.presheaf.map i.op x := by
  rw [Modules.map_smul, map_resTop]

noncomputable def smulHom (s : Γ(X, ⊤)) (M : X.Modules) : M ⟶ M :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        (DistribSMul.toAddMonoidHom Γ(M, U.unop) (resTop s U.unop))
      naturality := fun {U V} i => by
        ext x
        exact (map_resTop_smul s M i.unop (x : Γ(M, U.unop))).symm }
    (fun U r m => smul_res_comm s M U.unop r m)⟩

@[scoped simp] lemma smulHom_app_apply (s : Γ(X, ⊤)) (M : X.Modules) (U : X.Opens) (x : Γ(M, U)) :
    (smulHom s M).app U x = resTop s U • x := rfl

@[reassoc] lemma smulHom_comp (s : Γ(X, ⊤)) {M N : X.Modules} (φ : M ⟶ N) :
    smulHom s M ≫ φ = φ ≫ smulHom s N := by
  ext U x
  change φ.app U ((smulHom s M).app U x) = (smulHom s N).app U (φ.app U x)
  rw [smulHom_app_apply, smulHom_app_apply, Hom.app_smul]

lemma smulHom_mul (s s' : Γ(X, ⊤)) (M : X.Modules) :
    smulHom (s * s') M = smulHom s' M ≫ smulHom s M := by
  ext U x
  change (smulHom (s * s') M).app U x = (smulHom s M).app U ((smulHom s' M).app U x)
  simp only [smulHom_app_apply, resTop, map_mul, mul_smul]

@[scoped simp] lemma smulHom_one (M : X.Modules) : smulHom (1 : Γ(X, ⊤)) M = 𝟙 M := by
  ext U x
  change (smulHom 1 M).app U x = x
  simp [smulHom_app_apply, resTop]

noncomputable def smulIso (s : Γ(X, ⊤)ˣ) (M : X.Modules) : M ≅ M where
  hom := smulHom (s : Γ(X, ⊤)) M
  inv := smulHom (↑s⁻¹ : Γ(X, ⊤)) M
  hom_inv_id := by rw [← smulHom_mul, Units.inv_mul, smulHom_one]
  inv_hom_id := by rw [← smulHom_mul, Units.mul_inv, smulHom_one]

noncomputable def unitOne (U : X.Opens) : Γ(unitModule X, U) := (1 : Γ(X, U))

def toΓ {U : X.Opens} (x : Γ(unitModule X, U)) : Γ(X, U) := x

lemma eq_toΓ_smul_unitOne {U : X.Opens} (x : Γ(unitModule X, U)) : x = toΓ x • unitOne U :=
  (mul_one (toΓ x)).symm

lemma map_unitOne {U V : X.Opens} (i : U ⟶ V) :
    (unitModule X).presheaf.map i.op (unitOne V) = unitOne U :=
  map_one (X.presheaf.map i.op).hom

lemma smulHom_app_top_one (u : unitModule X ⟶ unitModule X) :
    smulHom (u.app ⊤ (unitOne ⊤)) (unitModule X) = u := by
  ext U x
  change resTop (u.app ⊤ (unitOne ⊤)) U • x = u.app U x
  have h1 : u.app U (unitOne U) = resTop (u.app ⊤ (unitOne ⊤)) U := by
    have h := Hom.app_naturality u (homOfLE (le_top : U ≤ ⊤)) (unitOne ⊤)
    rw [map_unitOne] at h
    exact h
  rw [eq_toΓ_smul_unitOne x, Hom.app_smul, h1]
  change (resTop (u.app ⊤ (unitOne ⊤)) U * (toΓ x * 1) : Γ(X, U)) = toΓ x * resTop (u.app ⊤ (unitOne ⊤)) U
  ring

lemma app_top_comp_unitOne (u v : unitModule X ⟶ unitModule X) :
    toΓ ((u ≫ v).app ⊤ (unitOne ⊤)) = toΓ (u.app ⊤ (unitOne ⊤)) * toΓ (v.app ⊤ (unitOne ⊤)) := by
  conv_lhs => rw [← smulHom_app_top_one v]
  change toΓ ((smulHom (v.app ⊤ (unitOne ⊤)) (unitModule X)).app ⊤ (u.app ⊤ (unitOne ⊤))) = _
  rw [smulHom_app_apply, resTop_top]
  exact mul_comm _ _

noncomputable def unitOfAut (δ : unitModule X ≅ unitModule X) : Γ(X, ⊤)ˣ where
  val := toΓ (δ.hom.app ⊤ (unitOne ⊤))
  inv := toΓ (δ.inv.app ⊤ (unitOne ⊤))
  val_inv := by rw [← app_top_comp_unitOne, δ.hom_inv_id]; rfl
  inv_val := by rw [← app_top_comp_unitOne, δ.inv_hom_id]; rfl

lemma smulIso_unitOfAut (δ : unitModule X ≅ unitModule X) :
    smulIso (unitOfAut δ) (unitModule X) = δ := by
  ext : 1
  exact smulHom_app_top_one δ.hom

lemma resTop_appTop (f : X ⟶ Y) (s : Γ(Y, ⊤)) (U : Y.Opens) :
    resTop (f.appTop s) (f ⁻¹ᵁ U) = f.app U (resTop s U) := by
  simp only [resTop, Scheme.Hom.appTop, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

lemma pushforward_map_smulHom (f : X ⟶ Y) (s : Γ(Y, ⊤)) (P : X.Modules) :
    (pushforward f).map (smulHom (f.appTop s) P) = smulHom s ((pushforward f).obj P) := by
  ext U x
  change (smulHom (f.appTop s) P).app (f ⁻¹ᵁ U) x = resTop s U • x
  rw [smulHom_app_apply, resTop_appTop]
  rfl

lemma pullback_map_smulHom (f : X ⟶ Y) (s : Γ(Y, ⊤)) (M : Y.Modules) :
    (pullback f).map (smulHom s M) = smulHom (f.appTop s) ((pullback f).obj M) := by
  apply ((pullbackPushforwardAdjunction f).homEquiv M ((pullback f).obj M)).injective
  have h1 := (pullbackPushforwardAdjunction f).unit.naturality (smulHom s M)
  dsimp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at h1
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  erw [← h1, pushforward_map_smulHom]
  exact smulHom_comp _ _

lemma pullback_mapIso_smulIso (f : X ⟶ Y) (s : Γ(Y, ⊤)ˣ) (M : Y.Modules) :
    (pullback f).mapIso (smulIso s M) = smulIso (Units.map (f.appTop).hom.toMonoidHom s) ((pullback f).obj M) := by
  ext : 1
  exact pullback_map_smulHom f s M

lemma appTop_appTop_of_comp_eq_id {T P : Scheme.{u}} (e : T ⟶ P) (p : P ⟶ T) (h : e ≫ p = 𝟙 T) (d : Γ(T, ⊤)) :
    e.appTop (p.appTop d) = d := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  rw [h]
  simp

end AlgebraicGeometry.Scheme.Modules
w03_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective.AlgebraicGeometry.Scheme P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective.AlgebraicGeometry.Scheme.Modules"
w03_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective.AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective.AlgebraicGeometry.Scheme"
w03_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective.AlgebraicGeometry"

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective.AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra"
open _root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective.AlgebraicGeometry.Scheme.Modules in
r2nos_open_dual "_root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective.AlgebraicGeometry.Scheme.Modules" in

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (hp : Function.Surjective (pullback.snd c t).appTop)
    (M M' : RigidifiedLineBundle c ε t)
    (α : (Scheme.Modules.pullback (rigSection c t ε)).obj M.L ≅ SheafOfModules.unit T.ringCatSheaf)
    (α' : (Scheme.Modules.pullback (rigSection c t ε)).obj M'.L ≅ SheafOfModules.unit T.ringCatSheaf)
    (φ ψ : M.L ≅ M'.L)
    (hφ : (Scheme.Modules.pullback (rigSection c t ε)).mapIso φ ≪≫ α' = α)
    (hψ : (Scheme.Modules.pullback (rigSection c t ε)).mapIso ψ ≪≫ α' = α) :
    φ = ψ := by
  have hep : rigSection c t ε ≫ pullback.snd c t = 𝟙 T := pullback.lift_snd _ _ _

  have hF : (Scheme.Modules.pullback (rigSection c t ε)).map φ.hom =
      (Scheme.Modules.pullback (rigSection c t ε)).map ψ.hom := by
    have h := congrArg Iso.hom (hφ.trans hψ.symm)
    simp only [Iso.trans_hom, Functor.mapIso_hom] at h
    simpa using h =≫ α'.inv

  have hγ : (Scheme.Modules.pullback (rigSection c t ε)).map (φ.hom ≫ ψ.inv) = 𝟙 _ := by
    rw [Functor.map_comp, hF, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]

  obtain ⟨s, hs, -⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.existsUnique_app_eq_smul M.isInvertible (φ.hom ≫ ψ.inv)
  have hγs : φ.hom ≫ ψ.inv = smulHom s M.L := by
    ext U x
    exact hs U x

  have h1 : (rigSection c t ε).appTop s = 1 := by
    have h := hγ
    rw [hγs, pullback_map_smulHom] at h
    have h' : smulHom ((rigSection c t ε).appTop s) (unitModule T) = 𝟙 _ := by
      have hc := smulHom_comp ((rigSection c t ε).appTop s) α.hom
      rw [h, Category.id_comp] at hc
      calc smulHom ((rigSection c t ε).appTop s) (unitModule T)
          = α.inv ≫ α.hom ≫ smulHom ((rigSection c t ε).appTop s) (unitModule T) := by simp
        _ = 𝟙 _ := by rw [← hc, Iso.inv_hom_id]
    have h'' := congrArg (fun u => toΓ (Scheme.Modules.Hom.app u ⊤ (unitOne ⊤))) h'
    simp only [smulHom_app_apply, resTop_top, Scheme.Modules.Hom.id_app] at h''
    have h3 : ((rigSection c t ε).appTop s * 1 : Γ(T, ⊤)) = 1 := h''
    simpa using h3

  obtain ⟨d, hd⟩ := hp s
  have hd1 : d = 1 := by
    rw [← appTop_appTop_of_comp_eq_id _ _ hep d, hd, h1]
  have hs1 : s = 1 := by rw [← hd, hd1, map_one]

  rw [hs1, smulHom_one] at hγs
  ext : 1
  simpa using hγs =≫ ψ.hom
end S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_iso_eq_of_map_pullback_rigSection_comp_eq_of_surjective
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
