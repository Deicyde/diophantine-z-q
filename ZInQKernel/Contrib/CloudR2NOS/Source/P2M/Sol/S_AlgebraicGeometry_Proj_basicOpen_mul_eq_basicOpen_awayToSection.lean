/-
NEW EDITION (H5 lane4 a940f2af, 2026-11-17, Parent route (E)). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Proj_basicOpen_mul_eq_basicOpen_awayToSection.lean
  Source sha256  : 8d2468db4a461ee72ae9e2720bbc2e884eb445eb6ad28c580b1f5aed61c3ba49
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Proj_basicOpen_mul_eq_basicOpen_awayToSection
r2nos_namespace_dual

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry
r2nos_open_dual "CategoryTheory AlgebraicGeometry"

theorem solution
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {f g : A} {m m' : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (g_deg : g ∈ 𝒜 m') (hm' : 0 < m') :
    Proj.basicOpen 𝒜 (f * g) =
      (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (HomogeneousLocalization.Away.isLocalizationElem f_deg g_deg)) := by

  let V : (Proj 𝒜).Opens := Proj.basicOpen 𝒜 f
  let e : HomogeneousLocalization.Away 𝒜 f := HomogeneousLocalization.Away.isLocalizationElem f_deg g_deg
  let s : Γ(Proj 𝒜, V) := Proj.awayToSection 𝒜 f e

  have h1 : (Proj 𝒜).basicOpen s = V.ι ''ᵁ (V : Scheme.{u}).basicOpen (V.topIso.inv s) := by
    rw [Scheme.Opens.ι_image_basicOpen, Scheme.Opens.topIso_inv]
    exact (((Proj 𝒜).basicOpen_res s _).trans
      (inf_eq_right.mpr (((Proj 𝒜).basicOpen_le s).trans (Scheme.Opens.ι_image_top V).ge))).symm

  have h2 : V.topIso.inv s =
      (Proj.basicOpenToSpec 𝒜 f).appTop ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv e) := by
    show V.topIso.inv s = (Proj.basicOpenToSpec 𝒜 f).app ⊤ _
    rw [Proj.basicOpenToSpec_app_top]
    show V.topIso.inv s = V.topIso.inv (Proj.awayToSection 𝒜 f
      ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv e)))
    rw [Iso.inv_hom_id_apply]

  have h3' : (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv e) = PrimeSpectrum.basicOpen e :=
    basicOpen_eq_of_affine (R := CommRingCat.of (HomogeneousLocalization.Away 𝒜 f)) e
  have h4 : Proj.basicOpenToSpec 𝒜 f ⁻¹ᵁ (PrimeSpectrum.basicOpen e) = V.ι ⁻¹ᵁ Proj.basicOpen 𝒜 g := by
    have := Proj.awayι_preimage_basicOpen 𝒜 f_deg hm g_deg hm'
    rw [← Proj.basicOpenIsoSpec_inv_ι 𝒜 f f_deg hm, Scheme.Hom.comp_preimage] at this
    rw [← this, ← Scheme.Hom.comp_preimage, ← Proj.basicOpenIsoSpec_hom 𝒜 f f_deg hm, Iso.hom_inv_id,
      Scheme.Hom.id_preimage]
  calc Proj.basicOpen 𝒜 (f * g) = V ⊓ Proj.basicOpen 𝒜 g := Proj.basicOpen_mul 𝒜 f g
    _ = V.ι ''ᵁ (V.ι ⁻¹ᵁ Proj.basicOpen 𝒜 g) := by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    _ = V.ι ''ᵁ (Proj.basicOpenToSpec 𝒜 f ⁻¹ᵁ (PrimeSpectrum.basicOpen e)) := by rw [h4]
    _ = V.ι ''ᵁ (Proj.basicOpenToSpec 𝒜 f ⁻¹ᵁ (Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv e)) := by rw [h3']
    _ = V.ι ''ᵁ (V : Scheme.{u}).basicOpen ((Proj.basicOpenToSpec 𝒜 f).appTop
          ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv e)) := by
        rw [Scheme.preimage_basicOpen_top]
    _ = V.ι ''ᵁ (V : Scheme.{u}).basicOpen (V.topIso.inv s) := by rw [h2]
    _ = (Proj 𝒜).basicOpen s := h1.symm
end S_AlgebraicGeometry_Proj_basicOpen_mul_eq_basicOpen_awayToSection
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
