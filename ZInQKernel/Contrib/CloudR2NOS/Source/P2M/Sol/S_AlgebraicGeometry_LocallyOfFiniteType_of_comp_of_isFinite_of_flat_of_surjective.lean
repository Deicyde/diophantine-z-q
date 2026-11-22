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
  Source file    : P2M/Sol/S_AlgebraicGeometry_LocallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective.lean
  Source sha256  : 18a0158a578e29c0443851664c69928d81b0cedcf55c59a4f446d726b4ce86a9
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
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

import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Adjoin.Tower
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_LocallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective
r2nos_namespace_dual

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry"

theorem solution
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType (f ≫ g)] [IsFinite f]
    [Flat f] [Surjective f] [IsLocallyNoetherian Z] : LocallyOfFiniteType g := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFiniteType)]
  intro U V e
  have hV' : IsAffineOpen (f ⁻¹ᵁ (V : Y.Opens)) := V.2.preimage f
  let V' : X.affineOpens := ⟨f ⁻¹ᵁ (V : Y.Opens), hV'⟩
  have e' : (V' : X.Opens) ≤ (f ≫ g) ⁻¹ᵁ (U : Z.Opens) :=
    ((TopologicalSpace.Opens.map f.base).map (homOfLE e)).le

  let φAB := g.appLE U V e
  let φBC := f.appLE V V' le_rfl
  let φAC := (f ≫ g).appLE U V' e'
  have hcomp : φAB ≫ φBC = φAC := Scheme.Hom.appLE_comp_appLE f g U V V' e le_rfl

  have hAC : φAC.hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) _ ‹_› U V' e'

  have hBC : φBC.hom.Finite := by
    have := IsFinite.finite_app f V V.2
    rwa [Scheme.Hom.app_eq_appLE] at this

  have hBCflat : φBC.hom.Flat := HasRingHomProperty.appLE (P := @Flat) _ ‹_› V V' le_rfl
  have hBCsurj : Surjective (Spec.map φBC) := by
    refine ⟨fun q ↦ ?_⟩
    have hq : (V.2.fromSpec q : Y) ∈ (V : Y.Opens) :=
      V.2.range_fromSpec.le (Set.mem_range_self q)
    obtain ⟨x, hx⟩ := ‹Surjective f›.surj (V.2.fromSpec q)
    have hxV' : x ∈ (V' : X.Opens) := show f x ∈ (V : Y.Opens) by rw [hx]; exact hq
    obtain ⟨p, hp⟩ := hV'.range_fromSpec.ge hxV'
    refine ⟨p, V.2.fromSpec.isOpenEmbedding.injective ?_⟩
    have key := congrArg (fun h ↦ h p) (IsAffineOpen.SpecMap_appLE_fromSpec f V.2 hV' le_rfl)
    simp only [Scheme.Hom.comp_apply] at key
    change V.2.fromSpec (Spec.map φBC p) = V.2.fromSpec q
    rw [key, hp, hx]
  have hBCinj : Function.Injective φBC.hom :=
    ((flat_and_surjective_SpecMap_iff φBC).mp
      ⟨(HasRingHomProperty.Spec_iff (P := @Flat)).mpr hBCflat, hBCsurj⟩).injective

  algebraize [φAB.hom, φBC.hom, φAC.hom]
  have : IsScalarTower Γ(Z, U) Γ(Y, V) Γ(X, V') :=
    .of_algebraMap_eq' (by change φAC.hom = φBC.hom.comp φAB.hom; rw [← hcomp]; rfl)
  have : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian U
  have hfg := fg_of_fg_of_fg Γ(Z, U) Γ(Y, V) Γ(X, V') hAC.out Module.Finite.fg_top hBCinj
  exact ⟨hfg⟩
end S_AlgebraicGeometry_LocallyOfFiniteType_of_comp_of_isFinite_of_flat_of_surjective
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
