/- Additional modification notice, 2026-11-16: Cloud Batch 3 Worker 13
retargeted only repository module paths into the task-owned CloudB3W13
directories. Canonical mathematical declaration names and statements
are retained. Recovery and later compatibility changes are documented
in the accompanying source manifest and NOTICE. -/
/-
Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker.lean
  Retrieved      : 2026-11-14 (git smart-protocol blob, byte-for-byte; sha256 in lane4 port manifest)
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679, 2026-11-14).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or
omitted unless listed under manual repairs:
  * 1 `_root_.X` added next to `X` in `open … in` command(s) for namespaces the port splits (parse-time scoped syntax of Mathlib's `X`, as the single source namespace provided).
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 3 `r2nos_open_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (Lean closes these implicitly at EOF in the original; no-op).
  * file-level `set_option`s inserted after the port namespace, reproducing the source build environment: autoImplicit false (source lakefile.lean leanOptions); maxHeartbeats 4000000 (source lakefile.lean leanOptions); synthInstance.maxHeartbeats 400000 (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.types false (source lakefile.lean leanOptions); backward.isDefEq.respectTransparency.instanceSearchTypes false (Lean 4.35 option absent from source Lean 4.33.1; `false` restores 4.33.1 behaviour).
  * `import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudB3W13Shared.R2NOS.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker
r2nos_namespace_dual

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace"

universe u

namespace P2mReducedInduced
r2nos_namespace_dual

open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData
r2nos_open_dual "AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.IdealSheafData"

variable {X : Scheme.{u}}

theorem isRadical_vanishingIdeal_ideal (Z : Closeds X) (U : X.affineOpens) :
    ((vanishingIdeal Z).ideal U).IsRadical := by
  rw [vanishingIdeal_ideal]
  exact PrimeSpectrum.isRadical_vanishingIdeal _

theorem isReduced_subscheme_vanishingIdeal (Z : Closeds X) :
    IsReduced (vanishingIdeal Z).subscheme := by
  let I := vanishingIdeal Z
  have h : ∀ U : X.affineOpens, IsReduced (I.subschemeCover.openCover.X U) := by
    intro U
    have : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced _).mp (isRadical_vanishingIdeal_ideal Z U)
    show IsReduced (Spec (.of (Γ(X, U) ⧸ I.ideal U)))
    infer_instance
  exact IsReduced.of_openCover _ I.subschemeCover.openCover

theorem range_subschemeι_vanishingIdeal (Z : Closeds X) :
    Set.range (vanishingIdeal Z).subschemeι = (Z : Set X) := by
  rw [range_subschemeι]
  rfl

theorem basicOpen_inter_eq_empty_of_mem_vanishingIdeal (Z : Closeds X) (U : X.affineOpens)
    {s : Γ(X, U)} (hs : s ∈ (vanishingIdeal Z).ideal U) :
    (X.basicOpen s : Set X) ∩ Z = ∅ := by
  rw [vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal] at hs
  ext z
  simp only [Set.mem_inter_iff, SetLike.mem_coe, Set.mem_empty_iff_false, iff_false, not_and]
  intro hz hzZ
  have hzU : z ∈ (U : Set X) := X.basicOpen_le s hz
  rw [← U.2.range_fromSpec] at hzU
  obtain ⟨p, rfl⟩ := hzU
  have hp : s ∈ p.asIdeal := hs p hzZ
  have hp' : p ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen s := hz
  rw [U.2.fromSpec_preimage_basicOpen] at hp'
  exact absurd hp ((PrimeSpectrum.mem_basicOpen _ _).mp hp')

theorem vanishingIdeal_le_ker {T : Scheme.{u}} [IsReduced T] (Z : Closeds X) (f : T ⟶ X)
    (hf : Set.range f ⊆ Z) : vanishingIdeal Z ≤ f.ker := by
  rw [Scheme.Hom.ker, le_ofIdeals_iff]
  intro U s hs
  rw [RingHom.mem_ker]
  have hb : T.basicOpen ((f.app U).hom s) = ⊥ := by
    rw [← Scheme.preimage_basicOpen]
    ext t
    simp only [Scheme.Hom.coe_preimage, Set.mem_preimage, SetLike.mem_coe, Opens.coe_bot,
      Set.mem_empty_iff_false, iff_false]
    intro ht
    have hmem : f t ∈ (X.basicOpen s : Set X) ∩ Z := ⟨ht, hf ⟨t, rfl⟩⟩
    rw [basicOpen_inter_eq_empty_of_mem_vanishingIdeal Z U hs] at hmem
    exact hmem
  exact (basicOpen_eq_bot_iff _).mp hb

theorem exists_lift_subschemeι_vanishingIdeal {T : Scheme.{u}} [IsReduced T] (Z : Closeds X)
    (f : T ⟶ X) (hf : Set.range f ⊆ Z) :
    ∃! g : T ⟶ (vanishingIdeal Z).subscheme, g ≫ (vanishingIdeal Z).subschemeι = f := by
  refine ⟨IsClosedImmersion.lift (vanishingIdeal Z).subschemeι f ?_,
    IsClosedImmersion.lift_fac _ _ _, ?_⟩
  · rw [ker_subschemeι]
    exact vanishingIdeal_le_ker Z f hf
  · intro g hg
    rw [← cancel_mono (vanishingIdeal Z).subschemeι, hg, IsClosedImmersion.lift_fac]

end P2mReducedInduced

open P2mReducedInduced AlgebraicGeometry.Scheme.IdealSheafData _root_.AlgebraicGeometry.Scheme.IdealSheafData in
r2nos_open_dual "P2mReducedInduced AlgebraicGeometry.Scheme.IdealSheafData _root_.AlgebraicGeometry.Scheme.IdealSheafData" in
theorem solution {X : Scheme.{u}} (Z : TopologicalSpace.Closeds X) :
    IsReduced (vanishingIdeal Z).subscheme ∧
      ∀ {T : Scheme.{u}} [IsReduced T] (f : T ⟶ X), Set.range f ⊆ Z →
        vanishingIdeal Z ≤ f.ker :=
  ⟨isReduced_subscheme_vanishingIdeal Z, fun f hf => vanishingIdeal_le_ker Z f hf⟩

end S_AlgebraicGeometry_Scheme_IdealSheafData_isReduced_subscheme_vanishingIdeal_and_le_ker
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
