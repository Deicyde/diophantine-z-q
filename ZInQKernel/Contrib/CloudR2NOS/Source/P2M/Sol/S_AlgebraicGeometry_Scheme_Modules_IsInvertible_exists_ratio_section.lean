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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ratio_section.lean
  Source sha256  : 14eb59cb0514111918958e3d1a6c51a5eae10c94fe642124f30bf6bebbafb30d
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 5 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 4 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ratio_section
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ratio_section.AlgebraicGeometry CategoryTheory.MonoidalCategory Opposite"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.Modules.Hom.app_smul Scheme.Opens.ι_appIso Scheme.Modules.Hom Scheme.Modules.mapPresheaf_app Scheme Scheme.Opens.topIso_hom Scheme.Modules Scheme.Opens Scheme.Opens.ι_image_top Scheme.Modules.map_smul Scheme.Modules.coeff Scheme.Modules.zeroSchemeIdeal Scheme.Modules.IsInvertible Scheme.Modules.IsInvertible.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul Hom Γ Opens.ι_appIso topIso_hom Modules.Hom topIso Modules.mapPresheaf_app Opens.topIso_hom affineOpens Modules Opens Opens.ι_image_top Modules.map_smul restrict Modules.coeff Modules.zeroSchemeIdeal Modules.IsInvertible Modules.IsInvertible.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul presheaf Hom mapPresheaf_app restrict map_smul toUnitSection ofUnitSection ofUnitSection_smul restrictSection coeff zeroSchemeIdeal IsInvertible IsInvertible.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal"
namespace RATIO
r2nos_namespace_dual
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

noncomputable section

variable {X : Scheme.{u}}

lemma ringMap_map {W₁ W₂ W₃ : X.Opens} (k₁ : op W₁ ⟶ op W₂) (k₂ : op W₂ ⟶ op W₃) (k : op W₁ ⟶ op W₃)
    (a : Γ(X, W₁)) : X.presheaf.map k₂ (X.presheaf.map k₁ a) = X.presheaf.map k a := by
  rw [show k = k₁ ≫ k₂ from Quiver.Hom.unop_inj (Subsingleton.elim _ _), X.presheaf.map_comp]
  rfl

lemma map_map (M : X.Modules) {W₁ W₂ W₃ : X.Opens} (k₁ : op W₁ ⟶ op W₂) (k₂ : op W₂ ⟶ op W₃)
    (k : op W₁ ⟶ op W₃) (m : Γ(M, W₁)) : M.presheaf.map k₂ (M.presheaf.map k₁ m) = M.presheaf.map k m := by
  rw [show k = k₁ ≫ k₂ from Quiver.Hom.unop_inj (Subsingleton.elim _ _), M.presheaf.map_comp]
  rfl

lemma app_map {M N : X.Modules} (φ : M ⟶ N) {W' W : X.Opens} (i : W' ⟶ W) (m : Γ(M, W)) :
    φ.app W' (M.presheaf.map i.op m) = N.presheaf.map i.op (φ.app W m) := by
  have hnat := φ.mapPresheaf.naturality i.op
  have hx := ConcreteCategory.congr_hom hnat m
  simp only [ConcreteCategory.comp_apply, Scheme.Modules.mapPresheaf_app] at hx
  exact hx

variable {M : X.Modules}

abbrev σ (s : 𝟙_ X.Modules ⟶ M) : Γ(M, ⊤) := s.app ⊤ (toUnitSection ⊤ 1)

lemma restrictSection_eq (s : 𝟙_ X.Modules ⟶ M) (U : X.Opens) :
    restrictSection s U = M.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op (σ s) := by
  change s.app (U.ι ''ᵁ ⊤) (toUnitSection (U.ι ''ᵁ ⊤) 1) = _
  have h0 : toUnitSection (U.ι ''ᵁ ⊤) (1 : Γ(X, U.ι ''ᵁ ⊤)) =
      (𝟙_ X.Modules).presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op (toUnitSection ⊤ 1) := by
    change toUnitSection (U.ι ''ᵁ ⊤) (1 : Γ(X, U.ι ''ᵁ ⊤)) =
      toUnitSection _ (X.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op (1 : Γ(X, ⊤)))
    rw [map_one]
  rw [h0, app_map]

theorem main (hM : Scheme.Modules.IsInvertible M) (s t : 𝟙_ X.Modules ⟶ M) :
    ∃ r : Γ(X, (Scheme.Modules.zeroSchemeIdeal t).support.compl),
      ∀ (U : X.affineOpens) (hU : U.1 ≤ (Scheme.Modules.zeroSchemeIdeal t).support.compl)
        (τ : M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules),
        (X.presheaf.map (homOfLE hU).op).hom r * Scheme.Modules.coeff t U.1 τ.hom =
          Scheme.Modules.coeff s U.1 τ.hom := by
  set V : X.Opens := (Scheme.Modules.zeroSchemeIdeal t).support.compl with hV
  have hdisj : Disjoint (V : Set X) (Scheme.Modules.zeroSchemeIdeal t).support := by
    rw [Set.disjoint_iff]
    rintro x ⟨hxV, hxZ⟩
    exact hxV hxZ
  have hframe := AlgebraicGeometry.Scheme.Modules.IsInvertible.isFrameOn_app_of_disjoint_support_zeroSchemeIdeal
    hM t V hdisj
  obtain ⟨r, hr, -⟩ := hframe.existsUnique (W := V) le_top le_rfl
    (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ s))
  refine ⟨r, fun U hU τ => ?_⟩

  have hW'V : U.1.ι ''ᵁ ⊤ ≤ V := by rw [Scheme.Opens.ι_image_top]; exact hU

  have hr' : (X.presheaf.map (homOfLE hW'V).op r) •
      M.presheaf.map (homOfLE (le_top : U.1.ι ''ᵁ ⊤ ≤ ⊤)).op (σ t) =
        M.presheaf.map (homOfLE (le_top : U.1.ι ''ᵁ ⊤ ≤ ⊤)).op (σ s) := by
    have h := congrArg (M.presheaf.map (homOfLE hW'V).op) hr
    rw [Scheme.Modules.map_smul, map_map M _ _ (homOfLE (le_top : U.1.ι ''ᵁ ⊤ ≤ ⊤)).op,
      map_map M _ _ (homOfLE (le_top : U.1.ι ''ᵁ ⊤ ≤ ⊤)).op] at h
    exact h

  let A := Γ((U.1 : Scheme.{u}), (⊤ : (U.1 : Scheme.{u}).Opens))
  let N := Γ(M.restrict U.1.ι, (⊤ : (U.1 : Scheme.{u}).Opens))

  have hXN : ∀ (a : Γ(X, U.1.ι ''ᵁ ⊤)) (m : Γ(M, U.1.ι ''ᵁ ⊤)), a • m = @HSMul.hSMul A N N _ a m := by
    intro a m
    change _ = (((U.1.ι.appIso ⊤).inv a : Γ(X, U.1.ι ''ᵁ ⊤)) • m : Γ(M, U.1.ι ''ᵁ ⊤))
    (simp [Scheme.Opens.ι_appIso]; rfl)
  have key : restrictSection s U.1 =
      @HSMul.hSMul A N N _ (X.presheaf.map (homOfLE hW'V).op r) (restrictSection t U.1) := by
    rw [restrictSection_eq s U.1, restrictSection_eq t U.1, ← hXN]
    exact hr'.symm

  change (X.presheaf.map (homOfLE hU).op).hom r *
      U.1.topIso.hom (ofUnitSection ⊤ (τ.hom.app ⊤ (restrictSection t U.1))) =
    U.1.topIso.hom (ofUnitSection ⊤ (τ.hom.app ⊤ (restrictSection s U.1)))
  rw [key, Scheme.Modules.Hom.app_smul, ofUnitSection_smul, map_mul]
  congr 1

  rw [Scheme.Opens.topIso_hom]
  exact (ringMap_map _ _ _ _).symm

end

end AlgebraicGeometry.Scheme.Modules.RATIO

theorem solution
    {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s t : 𝟙_ X.Modules ⟶ M) :
    ∃ r : Γ(X, (Scheme.Modules.zeroSchemeIdeal t).support.compl),
      ∀ (U : X.affineOpens) (hU : U.1 ≤ (Scheme.Modules.zeroSchemeIdeal t).support.compl)
        (τ : M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules),
        (X.presheaf.map (homOfLE hU).op).hom r * Scheme.Modules.coeff t U.1 τ.hom =
          Scheme.Modules.coeff s U.1 τ.hom :=
  AlgebraicGeometry.Scheme.Modules.RATIO.main hM s t
end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_ratio_section
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
