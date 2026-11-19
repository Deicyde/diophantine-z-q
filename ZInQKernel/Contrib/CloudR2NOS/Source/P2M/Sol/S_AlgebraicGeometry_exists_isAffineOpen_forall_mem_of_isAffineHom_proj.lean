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
  Source file    : P2M/Sol/S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj.lean
  Source sha256  : 2cca28e8f80b4edda5a45c25ce5672bdfdda01bbb5115311d29bb8d85dd93960
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_HomogeneousIdeal_exists_homogeneous_pos_mem_forall_notMem
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj
r2nos_namespace_dual

universe u v

open CategoryTheory
r2nos_open_dual "CategoryTheory"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme Proj.mem_basicOpen Proj Proj.isAffineOpen_basicOpen Proj.basicOpen IsAffineOpen IsAffineHom"
w03_open "AlgebraicGeometry"
section ProjOpen
variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
namespace Proj
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Proj" "mem_basicOpen isAffineOpen_basicOpen basicOpen"
end Proj
r2nos_open_scoped "AlgebraicGeometry.Proj" in

theorem Proj.exists_basicOpen_le_forall_mem_of_finset (U : (Proj 𝒜).Opens) (S : Finset (Proj 𝒜))
    (hS : ∀ x ∈ S, x ∈ U) :
    ∃ (n : ℕ) (f : A), 0 < n ∧ f ∈ 𝒜 n ∧ Proj.basicOpen 𝒜 f ≤ U ∧ ∀ x ∈ S, x ∈ Proj.basicOpen 𝒜 f := by
  classical
  set Z : Set (Proj 𝒜) := (U : Set (Proj 𝒜))ᶜ with hZdef
  have hZ : IsClosed Z := U.isOpen.isClosed_compl
  set J : HomogeneousIdeal 𝒜 := ProjectiveSpectrum.vanishingIdeal Z with hJdef
  have hZJ : ProjectiveSpectrum.zeroLocus 𝒜 (J : Set A) = Z := by
    rw [hJdef, ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hZ.closure_eq
  have havoid : ∀ p ∈ S.image (fun x : Proj 𝒜 => x.asHomogeneousIdeal),
      ¬ (J ⊓ HomogeneousIdeal.irrelevant 𝒜 ≤ p) := by
    intro p hp hle
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hp
    change (J ⊓ HomogeneousIdeal.irrelevant 𝒜).toIdeal ≤ x.asHomogeneousIdeal.toIdeal at hle
    rw [HomogeneousIdeal.toIdeal_inf, x.isPrime.inf_le] at hle
    rcases hle with hle | hle
    ·
      have hxZ : x ∈ Z := by
        rw [← hZJ]
        exact (ProjectiveSpectrum.mem_zeroLocus 𝒜 x _).mpr hle
      exact hxZ (hS x hxS)
    · exact x.not_irrelevant_le hle
  obtain ⟨n, f, hn, hfn, hfI, hf⟩ :=
    (J ⊓ HomogeneousIdeal.irrelevant 𝒜).exists_homogeneous_pos_mem_forall_notMem inf_le_right
      (S.image fun x : Proj 𝒜 => x.asHomogeneousIdeal)
      (fun p hp => by
        obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hp
        exact x.isPrime)
      havoid
  refine ⟨n, f, hn, hfn, ?_, ?_⟩
  · intro y hy
    by_contra hyU
    have hyZ : y ∈ Z := hyU
    rw [← hZJ] at hyZ
    have hfJ : f ∈ J := (inf_le_left : J ⊓ HomogeneousIdeal.irrelevant 𝒜 ≤ J) hfI
    exact (Proj.mem_basicOpen 𝒜 f y).mp hy ((ProjectiveSpectrum.mem_zeroLocus 𝒜 y _).mp hyZ hfJ)
  · intro x hx
    rw [Proj.mem_basicOpen]
    exact hf _ (Finset.mem_image_of_mem _ hx)

end ProjOpen
end AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj.AlgebraicGeometry in
r2nos_open_dual "_root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj.AlgebraicGeometry" in
theorem solution
    {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {X : AlgebraicGeometry.Scheme.{u}} (ι : X ⟶ AlgebraicGeometry.Proj 𝒜) [AlgebraicGeometry.IsAffineHom ι]
    (S : Finset X) :
    ∃ W : X.Opens, AlgebraicGeometry.IsAffineOpen W ∧ ∀ x ∈ S, x ∈ W := by
  classical
  obtain ⟨n, f, hn, hfn, -, hmem⟩ :=
    AlgebraicGeometry.Proj.exists_basicOpen_le_forall_mem_of_finset 𝒜 ⊤ (S.image ι.base) (fun _ _ => trivial)
  exact ⟨ι ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f, (AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒜 f hfn hn).preimage ι,
    fun x hx => hmem _ (Finset.mem_image_of_mem _ hx)⟩
end S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_isAffineHom_proj
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
