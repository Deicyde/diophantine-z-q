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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_app_eq_smul.lean
  Source sha256  : 5f22ff993c1a416ed54ce09b9a42afbeb072c18a940bcde7fc03e34755b5eefa
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_app_eq_smul
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry TopologicalSpace Opposite"

namespace ZSWs13
r2nos_namespace_dual

variable {X : Scheme.{u}} {M : X.Modules}

theorem map_app_unit (φ : 𝟙_ X.Modules ⟶ M) {U V : X.Opens} (i : U ⟶ V)
    (m : Γ(𝟙_ X.Modules, V)) :
    M.presheaf.map i.op (φ.app V m) = φ.app U ((𝟙_ X.Modules).presheaf.map i.op m) := by
  have h := (Scheme.Modules.Hom.mapPresheaf φ).naturality i.op
  have h2 := ConcreteCategory.congr_hom h m
  simp only [Scheme.Modules.mapPresheaf_app, ConcreteCategory.comp_apply] at h2
  exact h2.symm

theorem map_toUnitSection_one {U V : X.Opens} (i : U ⟶ V) :
    (𝟙_ X.Modules).presheaf.map i.op (Scheme.Modules.toUnitSection V 1) =
      Scheme.Modules.toUnitSection U 1 := by
  apply Scheme.Modules.ofUnitSection_injective
  rw [Scheme.Modules.ofUnitSection_map, Scheme.Modules.ofUnitSection_toUnitSection,
    Scheme.Modules.ofUnitSection_toUnitSection, map_one]

theorem app_one_eq_map (φ : 𝟙_ X.Modules ⟶ M) (U : X.Opens) :
    φ.app U (Scheme.Modules.toUnitSection U 1) =
      M.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (φ.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) := by
  rw [map_app_unit, map_toUnitSection_one]

end ZSWs13

open ZSWs13 in
r2nos_open_dual "ZSWs13" in
theorem solution
    {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M)
    (s₁ s₂ : 𝟙_ X.Modules ⟶ M) (u : Γ(X, ⊤)) (hu : IsUnit u)
    (h : s₂.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = u • s₁.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) :
    Scheme.Modules.zeroSchemeIdeal s₁ = Scheme.Modules.zeroSchemeIdeal s₂ := by
  classical

  have hcov : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ Nonempty (M.restrict U.1.ι ≅ 𝟙_ (U.1 : Scheme.{u}).Modules) := by
    intro x
    obtain ⟨U, hxU, -, hτ⟩ := hM.exists_restrict_iso (V := ⊤) (x := x) trivial
    exact ⟨U, hxU, hτ⟩
  choose U hxU hτ using hcov
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top U
    (top_le_iff.mp fun x _ => Opens.mem_iSup.mpr ⟨x, hxU x⟩) fun x => ?_
  obtain ⟨τ⟩ := hτ x
  obtain ⟨-, h1⟩ := Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq hM s₁
  obtain ⟨-, h2⟩ := Scheme.Modules.IsInvertible.coeffIdeal_le_and_ideal_zeroSchemeIdeal_eq hM s₂
  rw [(h1 (U x) τ).1, (h2 (U x) τ).1]

  set W : X.Opens := (U x).1.ι ''ᵁ ⊤ with hW
  have hres : s₂.app W (Scheme.Modules.toUnitSection W 1) =
      X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op u • s₁.app W (Scheme.Modules.toUnitSection W 1) := by
    rw [app_one_eq_map s₂ W, app_one_eq_map s₁ W, h, Scheme.Modules.map_smul]

  set r : Γ(((U x).1 : Scheme.{u}), ⊤) := ((U x).1.ι.appIso ⊤).hom (X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op u) with hr
  have hr' : ((U x).1.ι.appIso ⊤).inv r = X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op u := by
    rw [hr, Iso.hom_inv_id_apply]
  have hres' : Scheme.Modules.restrictSection s₂ (U x).1 = r • Scheme.Modules.restrictSection s₁ (U x).1 := by
    change s₂.app W (Scheme.Modules.toUnitSection W 1) =
      ((U x).1.ι.appIso ⊤).inv r • s₁.app W (Scheme.Modules.toUnitSection W 1)
    rw [hr']
    exact hres
  have hru : IsUnit r := (hu.map _).map _
  have key : Scheme.Modules.coeff s₂ (U x).1 τ.hom = (U x).1.topIso.hom r * Scheme.Modules.coeff s₁ (U x).1 τ.hom := by
    show (U x).1.topIso.hom (Scheme.Modules.ofUnitSection ⊤ (τ.hom.app ⊤ (Scheme.Modules.restrictSection s₂ (U x).1))) = _
    rw [hres', Scheme.Modules.Hom.app_smul, Scheme.Modules.ofUnitSection_smul, map_mul]
    rfl
  rw [key]
  exact (Ideal.span_singleton_mul_left_unit (hru.map _) _).symm
end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_eq_of_app_eq_smul
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
