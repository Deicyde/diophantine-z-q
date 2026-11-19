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
  Source file    : P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot.lean
  Source sha256  : 823ba10a56b14649e4cadc6a1d4a8ac8bf172c7b86e0da9aa6b6fd40847ed5b6
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 6400000`; `set_option synthInstance.maxHeartbeats 1600000`; `set_option linter.unusedSectionVars false`; `set_option linter.unusedSimpArgs false`; `set_option linter.unusedVariables false`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot
r2nos_namespace_dual

set_option autoImplicit false

w03_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite"

noncomputable section

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "IsLocallyNoetherian Scheme.IdealSheafData.coe_support_vanishingIdeal Scheme.preimage_basicOpen Spec Scheme.IdealSheafData.range_subschemeι Scheme Scheme.IdealSheafData.vanishingIdeal Scheme.basicOpen_zero IsLocallyNoetherian.component_noetherian IsNoetherian Scheme.IdealSheafData OModulePresheaf.idealPowSub OModulePresheaf OModulePresheaf.IsCoherent OModulePresheaf.IsQuasicoherent OModulePresheaf.SupportedIn Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.algebraOfHom"
namespace OModulePresheaf
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf" "idealSections idealSections_eq_ideal idealPowSub IsCoherent IsQuasicoherent SupportedIn isScalarTower obj"
namespace G4T
r2nos_namespace_dual
w03_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

universe u

theorem support_vanishingIdeal {V : Scheme.{u}} (Z : Closeds V) : (Scheme.IdealSheafData.vanishingIdeal Z).support = Z :=
  SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)

section Terminates

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

theorem basicOpen_disjoint_of_mem_vanishingIdeal (Y : Closeds V)
    (U : V.affineOpens) (f : Γ(V, U.1))
    (hf : f ∈ (Scheme.IdealSheafData.vanishingIdeal Y).ideal U) :
    ((V.basicOpen f : V.Opens) : Set V) ∩ Y = ∅ := by
  set iY := (Scheme.IdealSheafData.vanishingIdeal Y).subschemeι
  have hpre : iY ⁻¹ᵁ V.basicOpen f = ⊥ := by
    rw [Scheme.preimage_basicOpen,
      show (iY.app U.1).hom f = 0 from
        (idealSections_eq_ideal (Scheme.IdealSheafData.vanishingIdeal Y) U ▸ hf :
          f ∈ idealSections (Scheme.IdealSheafData.vanishingIdeal Y) U.1),
      Scheme.basicOpen_zero]
  have hrange : Set.range iY.base = (Y : Set V) :=
    (Scheme.IdealSheafData.range_subschemeι _).trans
      (congrArg SetLike.coe (support_vanishingIdeal Y))
  refine Set.eq_empty_of_forall_notMem fun x ⟨hxD, hxY⟩ => ?_
  obtain ⟨z, rfl⟩ := hrange ▸ hxY
  exact (congrArg (z ∈ ·) (congrArg SetLike.coe hpre)).mp hxD

theorem exists_idealPowSub_eq_bot [IsLocallyNoetherian V] (Y : Closeds V)
    (F : OModulePresheaf π) (hFc : OModulePresheaf.IsCoherent F)
    (hFq : OModulePresheaf.IsQuasicoherent F) (hFs : OModulePresheaf.SupportedIn F Y)
    (U : V.affineOpens) :
    ∃ N, idealPowSub π (Scheme.IdealSheafData.vanishingIdeal Y) F N U.1 = ⊥ := by
  letI := (Scheme.TwoAffineOpenCover.algebraOfHom π U.1).toModule; haveI := F.isScalarTower U.1
  haveI := IsLocallyNoetherian.component_noetherian U
  set I := Scheme.IdealSheafData.vanishingIdeal Y
  set ann : Ideal Γ(V, U.1) := Module.annihilator Γ(V, U.1) (F.obj U.1)

  have hrad : I.ideal U ≤ ann.radical := fun f hf => by
    have hDdisj := basicOpen_disjoint_of_mem_vanishingIdeal Y U f hf
    haveI := hFs ⟨V.basicOpen f, U.2.basicOpen f⟩ hDdisj
    have hann : ∀ y : F.obj U.1, ∃ n, (f ^ n : Γ(V, U.1)) • y = 0 :=
      fun y => (hFq U f).2 y (Subsingleton.elim _ _)
    obtain ⟨s, hs⟩ := Module.finite_def.mp (hFc U)
    choose ny hny using fun y : s => hann y
    refine ⟨s.attach.sup ny, Module.mem_annihilator.mpr fun y => ?_⟩
    have hy : y ∈ Submodule.span Γ(V, U.1) s := hs ▸ Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro z hz
      have hle : ny ⟨z, hz⟩ ≤ s.attach.sup ny := Finset.le_sup (Finset.mem_attach s ⟨z, hz⟩)
      rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hny ⟨z, hz⟩, smul_zero]
    · exact smul_zero _
    · exact fun _ _ _ _ ha hb => by rw [smul_add, ha, hb, add_zero]
    · exact fun c z _ hz => by rw [smul_comm, hz, smul_zero]

  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  refine ⟨N, le_bot_iff.mp fun x hx => ?_⟩
  rw [idealPowSub, Submodule.restrictScalars_mem,
    idealSections_eq_ideal] at hx
  exact Submodule.smul_induction_on hx
    (fun a ha z _ => (Module.mem_annihilator.mp (hN ha) z) ▸ Submodule.zero_mem _)
    (fun _ _ h₁ h₂ => Submodule.add_mem _ h₁ h₂)

end Terminates

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot.AlgebraicGeometry in
r2nos_open_dual "_root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot.AlgebraicGeometry" in
theorem solution {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsLocallyNoetherian V] (Y : TopologicalSpace.Closeds V) (F : OModulePresheaf π) (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hFs : F.SupportedIn Y) (U : V.affineOpens) : ∃ N : ℕ, OModulePresheaf.idealPowSub π (Scheme.IdealSheafData.vanishingIdeal Y) F N U.1 = ⊥ :=
  AlgebraicGeometry.OModulePresheaf.G4T.exists_idealPowSub_eq_bot π Y F hFc hFq hFs U
end S_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
