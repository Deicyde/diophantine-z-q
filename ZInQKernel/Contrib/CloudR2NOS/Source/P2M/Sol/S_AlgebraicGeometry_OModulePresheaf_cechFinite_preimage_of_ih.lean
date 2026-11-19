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
  Source file    : P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_preimage_of_ih.lean
  Source sha256  : 73e3e2612d0601805e73e22fc8ad1eba3fe890012ac0615158e75b113fa17b0d
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_cechFinite_pushforward_iff
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.Finiteness.Basic
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_preimage_of_ih
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_preimage_of_ih.AlgebraicGeometry TopologicalSpace Opposite"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.Hom.map_appLE Scheme.IdealSheafData.coe_support_vanishingIdeal Scheme.Hom Scheme.preimage_basicOpen Spec Scheme.IdealSheafData.range_subschemeι Scheme Scheme.IdealSheafData.vanishingIdeal IsClosedImmersion Scheme.IdealSheafData Scheme.Hom.appLE_eq_app OModulePresheaf OModulePresheaf.cechFinite_pushforward_iff"
namespace OModulePresheaf
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf" "pushforward Hom CechFinite IsCoherent IsQuasicoherent SupportedIn res res_smul res_refl obj res_comp moduleSections cechFinite_pushforward_iff"
namespace Descend
r2nos_namespace_dual
w03_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

variable {R : Type u} [CommRing R] {V Z : Scheme.{u}} (π : V ⟶ Spec (.of R)) (i : Z ⟶ V) [IsClosedImmersion i]
variable (F : OModulePresheaf (i ≫ π))

theorem isCoherent_pushforward (hFc : F.IsCoherent) : (pushforward π i F).IsCoherent := fun U => by
  letI : Module Γ(V, U.1) (F.obj (i ⁻¹ᵁ U.1)) := (pushforward π i F).moduleSections U.1
  letI : Algebra Γ(V, U.1) Γ(Z, i ⁻¹ᵁ U.1) := (i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  haveI : IsScalarTower Γ(V, U.1) Γ(Z, i ⁻¹ᵁ U.1) (F.obj (i ⁻¹ᵁ U.1)) :=
    ⟨fun a b x => by show ((i.appLE U.1 _ le_rfl).hom a * b) • x = _; rw [mul_smul]; rfl⟩
  haveI : Module.Finite Γ(V, U.1) Γ(Z, i ⁻¹ᵁ U.1) :=
    Module.Finite.of_surjective (Algebra.linearMap _ _) fun x => by
      obtain ⟨a, ha⟩ := i.app_surjective U.1 U.2 x
      exact ⟨a, show (i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl).hom a = x by rw [Scheme.Hom.appLE_eq_app]; exact ha⟩
  haveI := hFc ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩
  exact Module.Finite.trans (R := Γ(V, U.1)) Γ(Z, i ⁻¹ᵁ U.1) (F.obj (i ⁻¹ᵁ U.1))

theorem isQuasicoherent_pushforward (hFq : F.IsQuasicoherent) : (pushforward π i F).IsQuasicoherent := fun U f => by
  letI : Module Γ(V, U.1) (F.obj (i ⁻¹ᵁ U.1)) := (pushforward π i F).moduleSections U.1
  set g : Γ(Z, i ⁻¹ᵁ U.1) := (i.app U.1).hom f with hg_def
  have hbo : i ⁻¹ᵁ V.basicOpen f = Z.basicOpen g := Scheme.preimage_basicOpen i f
  obtain ⟨hs, ha⟩ := hFq ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ g
  have hpow : ∀ n (y : F.obj (i ⁻¹ᵁ U.1)),
      (f ^ n : Γ(V, U.1)) • y = (g ^ n : Γ(Z, i ⁻¹ᵁ U.1)) • y := fun n y => by
    show (i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl).hom (f ^ n) • y = _
    rw [map_pow, Scheme.Hom.appLE_eq_app]
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨n, y, hny⟩ := hs (F.res hbo.ge (show F.obj (i ⁻¹ᵁ V.basicOpen f) from x))
    refine ⟨n, y, ?_⟩
    have key := congrArg (F.res hbo.le) hny
    rw [← LinearMap.comp_apply, ← F.res_comp, F.res_smul,
      ← LinearMap.comp_apply (g := F.res hbo.ge), ← F.res_comp,
      LinearMap.congr_fun (F.res_refl _) x] at key
    show F.res _ y = (i.appLE (V.basicOpen f) (i ⁻¹ᵁ V.basicOpen f) le_rfl).hom
        ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n))
      • (show F.obj (i ⁻¹ᵁ V.basicOpen f) from x)
    refine key.trans ?_
    congr 1
    rw [← CommRingCat.comp_apply (f := V.presheaf.map _), Scheme.Hom.map_appLE,
      ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp, map_pow, map_pow]
    congr 1
  · refine (ha y ?_).imp fun n hn => (hpow n y).trans hn
    refine (LinearMap.congr_fun (F.res_comp hbo.ge ((Opens.map i.base).monotone (V.basicOpen_le f))) y).trans ?_
    exact (congrArg (F.res hbo.ge)
      (show F.res ((Opens.map i.base).monotone (V.basicOpen_le f)) y = 0 from hy)).trans (map_zero _)

theorem supportedIn_pushforward_image {Y' : Closeds Z} (hFs : F.SupportedIn Y') :
    (pushforward π i F).SupportedIn ⟨i.base '' Y', i.isClosedEmbedding.isClosedMap _ Y'.2⟩ := fun U hU =>
  hFs ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ (by
    refine Set.eq_empty_of_forall_notMem fun x ⟨hxU, hxY'⟩ => ?_
    exact Set.eq_empty_iff_forall_notMem.mp hU (i.base x) ⟨hxU, ⟨x, hxY', rfl⟩⟩)

end AlgebraicGeometry.OModulePresheaf.Descend

open AlgebraicGeometry.OModulePresheaf.Descend in
r2nos_open_dual "AlgebraicGeometry.OModulePresheaf.Descend" in

theorem solution
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (K : V.OrderedAffineCover)
    {Z₀ : TopologicalSpace.Closeds V}
    (ih : ∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' → G.CechFinite K)
    (F : OModulePresheaf ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ≫ π))
    (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent)
    (Y' : TopologicalSpace.Closeds (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme) (hY' : Y' < ⊤)
    (hFs : F.SupportedIn Y') :
    F.CechFinite (K.preimage (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι) := by
  have hrange : Set.range (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.base = (Z₀ : Set V) :=
    (Scheme.IdealSheafData.range_subschemeι _).trans (Scheme.IdealSheafData.coe_support_vanishingIdeal Z₀)
  let Y'' : Closeds V := ⟨(Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.base '' Y', (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.isClosedEmbedding.isClosedMap _ Y'.2⟩
  have hY''_lt : Y'' < Z₀ := by
    refine lt_of_le_of_ne (fun v ⟨_, _, hvx⟩ => show v ∈ (Z₀ : Set V) from hvx ▸ hrange ▸ Set.mem_range_self _)
      (fun heq => hY'.ne (SetLike.coe_injective (Set.eq_univ_of_forall fun x => ?_)))
    have hx : (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.base x ∈ (Y'' : Set V) :=
      heq.symm ▸ (show (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.base x ∈ (Z₀ : Set V) from hrange ▸ Set.mem_range_self x)
    obtain ⟨x', hx', hxx'⟩ := hx
    exact (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.isClosedEmbedding.injective hxx' ▸ hx'
  exact (AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_iff (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι F K).mp
    (ih Y'' hY''_lt _ (isCoherent_pushforward π _ F hFc) (isQuasicoherent_pushforward π _ F hFq)
      (supportedIn_pushforward_image π _ F hFs))
end S_AlgebraicGeometry_OModulePresheaf_cechFinite_preimage_of_ih
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
