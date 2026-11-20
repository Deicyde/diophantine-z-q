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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal.lean
  Source sha256  : 19a6d97836435e42280d142e685393b83e2ef3e748906b65fa3c9c29b4b39bf1
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 5 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
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
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_smul_of_forall_exists_bijective_smul
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal.AlgebraicGeometry"

open scoped CategoryTheory.MonObj
r2nos_open_scoped_dual "CategoryTheory.MonObj"

open Opposite TopologicalSpace
r2nos_open_dual "Opposite TopologicalSpace"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Opens.ι_appIso Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf RingedSpace.isUnit_res_basicOpen Scheme.Modules.mapPresheaf_app Scheme Scheme.Modules.Hom.id_app Scheme.Modules.restrict_map Scheme.Opens.topIso_hom Scheme.zeroLocus_span Scheme.mem_zeroLocus_iff Scheme.Modules Scheme.Opens Scheme.IdealSheafData.mem_support_iff_of_mem Scheme.Modules.map_smul Scheme.Opens.opensRange_ι RingedSpace Scheme.IdealSheafData Scheme.Modules.IsInvertible Scheme.Modules.IsFrameOn Scheme.Modules.toUnitSection Scheme.Modules.zeroSchemeIdeal"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul Hom.id_app Hom Γ Modules.Hom.comp_app Opens.ι_appIso topIso_hom Modules.Hom Hom.image_preimage_eq_opensRange_inf topIso Modules.mapPresheaf_app Modules.Hom.id_app Modules.restrict_map toLocallyRingedSpace Opens.topIso_hom zeroLocus zeroLocus_span mem_zeroLocus_iff Hom.comp_app basicOpen Modules Opens IdealSheafData.mem_support_iff_of_mem Modules.map_smul Opens.opensRange_ι basicOpen_le restrict IdealSheafData Modules.IsInvertible Modules.IsFrameOn Modules.toUnitSection Modules.zeroSchemeIdeal"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul presheaf Hom.comp_app Hom mapPresheaf_app Hom.id_app restrict_map restrict map_smul IsInvertible unitSection smul_unitSection IsFrameOn isFrameOn_unitSection toUnitSection ofUnitSection restrictSection coeff zeroSchemeIdeal bijective_smul_of_forall_exists_bijective_smul"
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace FrameOffZero
r2nos_namespace_dual

noncomputable section

variable {X : Scheme.{u}}

lemma map_congr (M : X.Modules) {W₁ W₂ : X.Opens} (k₁ k₂ : op W₂ ⟶ op W₁) (m : Γ(M, W₂)) :
    M.presheaf.map k₁ m = M.presheaf.map k₂ m := by
  rw [show k₁ = k₂ from Quiver.Hom.unop_inj (Subsingleton.elim _ _)]

lemma ringMap_congr {W₁ W₂ : X.Opens} (k₁ k₂ : op W₂ ⟶ op W₁) (a : Γ(X, W₂)) :
    X.presheaf.map k₁ a = X.presheaf.map k₂ a := by
  rw [show k₁ = k₂ from Quiver.Hom.unop_inj (Subsingleton.elim _ _)]

lemma ringMap_map {W₁ W₂ W₃ : X.Opens} (k₁ : op W₁ ⟶ op W₂) (k₂ : op W₂ ⟶ op W₃) (k : op W₁ ⟶ op W₃)
    (a : Γ(X, W₁)) : X.presheaf.map k₂ (X.presheaf.map k₁ a) = X.presheaf.map k a := by
  rw [show k = k₁ ≫ k₂ from Quiver.Hom.unop_inj (Subsingleton.elim _ _), X.presheaf.map_comp]
  rfl

lemma map_map (M : X.Modules) {W₁ W₂ W₃ : X.Opens} (k₁ : op W₁ ⟶ op W₂) (k₂ : op W₂ ⟶ op W₃)
    (k : op W₁ ⟶ op W₃) (m : Γ(M, W₁)) : M.presheaf.map k₂ (M.presheaf.map k₁ m) = M.presheaf.map k m := by
  rw [show k = k₁ ≫ k₂ from Quiver.Hom.unop_inj (Subsingleton.elim _ _), M.presheaf.map_comp]
  rfl

lemma image_preimage_eq_of_le {V W : X.Opens} (hW : W ≤ V) : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.2 hW]

lemma app_map {M N : X.Modules} (φ : M ⟶ N) {W' W : X.Opens} (i : W' ⟶ W) (m : Γ(M, W)) :
    φ.app W' (M.presheaf.map i.op m) = N.presheaf.map i.op (φ.app W m) := by
  have hnat := φ.mapPresheaf.naturality i.op
  have hx := ConcreteCategory.congr_hom hnat m
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at hx
  exact hx

def Q (M : X.Modules) (σ : Γ(M, ⊤)) (W : X.Opens) : Prop :=
  Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ : Γ(M, W))

section local_computation

variable {M : X.Modules} (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens)
  (τ : M.restrict U.ι ≅ 𝟙_ (U : Scheme.{u}).Modules)

abbrev σ : Γ(M, ⊤) := s.app ⊤ (toUnitSection ⊤ 1)

abbrev fr : Γ(M.restrict U.ι, ⊤) := τ.inv.app ⊤ (unitSection ⊤)

abbrev cU : Γ((U : Scheme.{u}), ⊤) := ofUnitSection ⊤ (τ.hom.app ⊤ (restrictSection s U))

lemma fr_isFrameOn : IsFrameOn (fr U τ) ⊤ :=
  (isFrameOn_unitSection (X := (U : Scheme.{u})) (U := ⊤) ⊤).map_iso τ.symm

lemma restrictSection_eq_smul : restrictSection s U = cU s U τ • fr U τ := by
  have h1 : τ.inv.app ⊤ (τ.hom.app ⊤ (restrictSection s U)) = restrictSection s U := by
    change (τ.hom.app ⊤ ≫ τ.inv.app ⊤) (restrictSection s U) = restrictSection s U
    rw [← Scheme.Modules.Hom.comp_app, τ.hom_inv_id, Scheme.Modules.Hom.id_app]
    rfl
  have h2 : τ.hom.app ⊤ (restrictSection s U) = cU s U τ • unitSection ⊤ := by
    rw [smul_unitSection]
    rfl
  rw [← h1, h2, Scheme.Modules.Hom.app_smul]

lemma map_σ_eq (W : (U : Scheme.{u}).Opens) :
    (M.presheaf.map (homOfLE (le_top : U.ι ''ᵁ W ≤ ⊤)).op (σ s) : Γ(M, U.ι ''ᵁ W)) =
      ((M.restrict U.ι).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (restrictSection s U) :
        Γ(M.restrict U.ι, W)) := by

  have h1 : restrictSection s U = M.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op (σ s) := by
    change s.app (U.ι ''ᵁ ⊤) (toUnitSection (U.ι ''ᵁ ⊤) 1) = _
    have h0 : toUnitSection (U.ι ''ᵁ ⊤) (1 : Γ(X, U.ι ''ᵁ ⊤)) =
        (𝟙_ X.Modules).presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op (toUnitSection ⊤ 1) := by
      change toUnitSection (U.ι ''ᵁ ⊤) (1 : Γ(X, U.ι ''ᵁ ⊤)) =
        toUnitSection _ (X.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op (1 : Γ(X, ⊤)))
      rw [map_one]
    rw [h0, app_map]
  rw [h1, Scheme.Modules.restrict_map]
  exact (map_map M _ _ _ _).symm

end local_computation

theorem main {M : X.Modules} (hM : IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (V : X.Opens) (hV : Disjoint (V : Set X) (zeroSchemeIdeal s).support) :
    IsFrameOn (s.app ⊤ (toUnitSection ⊤ 1)) V := by
  intro W hWtop hWV

  suffices key : ∀ x ∈ W, ∃ U' : X.Opens, x ∈ U' ∧ ∀ W' : X.Opens, W' ≤ U' → Q M (σ s) W' by
    exact bijective_smul_of_forall_exists_bijective_smul M (σ s) W key
  intro x hxW
  have hx : x ∉ ((zeroSchemeIdeal s).support : Set X) := Set.disjoint_left.mp hV (hWV hxW)

  obtain ⟨U, hxU, -, ⟨τ⟩⟩ := hM.exists_restrict_iso (V := ⊤) (x := x) trivial
  have hloc := ((hM.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq s).2 U τ).1

  have hxc : x ∈ X.basicOpen (coeff s U.1 τ.hom) := by
    have h1 : x ∉ X.zeroLocus (((zeroSchemeIdeal s).ideal U : Ideal Γ(X, U.1)) : Set Γ(X, U.1)) :=
      fun h => hx ((Scheme.IdealSheafData.mem_support_iff_of_mem hxU).mpr h)
    rw [hloc, Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff] at h1
    push Not at h1
    obtain ⟨f, hf, hxf⟩ := h1
    rw [Set.mem_singleton_iff] at hf
    exact hf ▸ hxf
  refine ⟨U.1 ⊓ X.basicOpen (coeff s U.1 τ.hom), ⟨hxU, hxc⟩, ?_⟩

  suffices himg : ∀ W : (U.1 : Scheme.{u}).Opens, U.1.ι ''ᵁ W ≤ X.basicOpen (coeff s U.1 τ.hom) →
      Q M (σ s) (U.1.ι ''ᵁ W) by
    intro W' hW'
    have e : U.1.ι ''ᵁ (U.1.ι ⁻¹ᵁ W') = W' := image_preimage_eq_of_le (hW'.trans inf_le_left)
    have h := himg (U.1.ι ⁻¹ᵁ W') (e.symm ▸ hW'.trans inf_le_right)
    rw [e] at h
    exact h
  intro W hWc

  let A := Γ((U.1 : Scheme.{u}), W)
  let N := Γ(M.restrict U.1.ι, W)

  have hXN : ∀ (a : Γ(X, U.1.ι ''ᵁ W)) (m : Γ(M, U.1.ι ''ᵁ W)), a • m = @HSMul.hSMul A N N _ a m := by
    intro a m
    change _ = (((U.1.ι.appIso W).inv a : Γ(X, U.1.ι ''ᵁ W)) • m : Γ(M, U.1.ι ''ᵁ W))
    (simp [Scheme.Opens.ι_appIso]; rfl)

  have hσ : (M.presheaf.map (homOfLE (le_top : U.1.ι ''ᵁ W ≤ ⊤)).op (σ s) : N) =
      @HSMul.hSMul A N N _ ((U.1 : Scheme.{u}).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (cU s U.1 τ))
        ((M.restrict U.1.ι).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (fr U.1 τ)) := by
    rw [map_σ_eq, restrictSection_eq_smul s U.1 τ, Scheme.Modules.map_smul]

  have hunit : IsUnit ((U.1 : Scheme.{u}).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (cU s U.1 τ)) := by

    have hc : (X.presheaf.map (homOfLE (hWc.trans (X.basicOpen_le _))).op (coeff s U.1 τ.hom) :
        Γ(X, U.1.ι ''ᵁ W)) = (U.1 : Scheme.{u}).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (cU s U.1 τ) := by
      change X.presheaf.map _ (U.1.topIso.hom (cU s U.1 τ)) = X.presheaf.map _ (cU s U.1 τ)
      rw [Scheme.Opens.topIso_hom]
      exact ringMap_map _ _ _ _
    rw [← hc]
    have h1 : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le (coeff s U.1 τ.hom))).op (coeff s U.1 τ.hom)) :=
      RingedSpace.isUnit_res_basicOpen (X := X.toLocallyRingedSpace.toRingedSpace) (coeff s U.1 τ.hom)
    have h2 := h1.map (X.presheaf.map (homOfLE hWc).op).hom
    have h3 : (X.presheaf.map (homOfLE hWc).op).hom
        (X.presheaf.map (homOfLE (X.basicOpen_le (coeff s U.1 τ.hom))).op (coeff s U.1 τ.hom)) =
        X.presheaf.map (homOfLE (hWc.trans (X.basicOpen_le _))).op (coeff s U.1 τ.hom) :=
      ringMap_map _ _ _ _
    rw [h3] at h2
    exact h2

  have hfr := (fr_isFrameOn U.1 τ) (W := W) le_top le_top
  have hmul : Function.Bijective fun g : A =>
      g * (U.1 : Scheme.{u}).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (cU s U.1 τ) :=
    (Units.mulRight hunit.unit).bijective
  have hcomp := hfr.comp hmul
  have hfun : (fun g : Γ(X, U.1.ι ''ᵁ W) =>
      g • (M.presheaf.map (homOfLE (le_top : U.1.ι ''ᵁ W ≤ ⊤)).op (σ s) : Γ(M, U.1.ι ''ᵁ W))) =
      (fun a : A => a • ((M.restrict U.1.ι).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (fr U.1 τ) : N)) ∘
        (fun g : A => g * (U.1 : Scheme.{u}).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (cU s U.1 τ)) := by
    funext g
    simp only [Function.comp_apply]
    rw [hXN, hσ, ← mul_smul]
  change Function.Bijective fun g : Γ(X, U.1.ι ''ᵁ W) =>
      g • (M.presheaf.map (homOfLE (le_top : U.1.ι ''ᵁ W ≤ ⊤)).op (σ s) : Γ(M, U.1.ι ''ᵁ W))
  rw [hfun]
  exact hcomp

end

end FrameOffZero

end AlgebraicGeometry.Scheme.Modules

theorem solution {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (V : X.Opens) (hV : Disjoint (V : Set X) (Scheme.Modules.zeroSchemeIdeal s).support) :
    Scheme.Modules.IsFrameOn (s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) V :=
  AlgebraicGeometry.Scheme.Modules.FrameOffZero.main hM s V hV
end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
