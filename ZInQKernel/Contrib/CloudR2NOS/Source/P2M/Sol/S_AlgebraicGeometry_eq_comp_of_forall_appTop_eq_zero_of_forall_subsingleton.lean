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
  Source file    : P2M/Sol/S_AlgebraicGeometry_eq_comp_of_forall_appTop_eq_zero_of_forall_subsingleton.lean
  Source sha256  : 6a2e4d477c233e7048e6e070772e62a80bfc544f770d2b4f027472cb933c58b9
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
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

namespace P2MW.S_AlgebraicGeometry_eq_comp_of_forall_appTop_eq_zero_of_forall_subsingleton
r2nos_namespace_dual

set_option autoImplicit false

w03_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_eq_comp_of_forall_appTop_eq_zero_of_forall_subsingleton.AlgebraicGeometry Opposite"
open Topology TopologicalSpace
r2nos_open_dual "Topology TopologicalSpace"

universe u

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.IdealSheafData.le_ofIdeals_iff Scheme.Hom pointOfClosedPoint_apply pointOfClosedPoint LocallyOfFiniteType Spec Scheme LocallyOfFiniteType.jacobsonSpace Scheme.Hom.ideal_ker_le Scheme.IdealSheafData.ker_subschemeι Scheme.Hom.comp_appTop pointOfClosedPoint_comp IsClosedImmersion IsClosedImmersion.lift IsClosedImmersion.lift_fac Scheme.Hom.ker IsAffineOpen Scheme.IdealSheafData.ofIdealTop Scheme.Hom.comp_apply Scheme.IdealSheafData.ofIdealTop_ideal Scheme.IdealSheafData"
namespace ArtinianPointsDetect
r2nos_namespace_dual
w03_open "AlgebraicGeometry"

section Sections

variable {X Y : Scheme.{u}}

theorem app_res_top (f : X ⟶ Y) (U : Y.Opens) (s : Γ(Y, ⊤)) :
    (f.app U).hom ((Y.presheaf.map (homOfLE (le_top (a := U))).op).hom s) =
      (X.presheaf.map (homOfLE (le_top (a := f ⁻¹ᵁ U))).op).hom (f.appTop.hom s) := by
  have h := f.naturality (homOfLE (le_top (a := U))).op
  have h' := congrArg (fun φ => φ.hom s) h
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h'
  rw [h']
  rfl

theorem appTop_eq_zero_of_forall_app (f : X ⟶ Y) (s : Γ(Y, ⊤))
    (h : ∀ U : Y.affineOpens,
      (f.app U.1).hom ((Y.presheaf.map (homOfLE (le_top (a := U.1))).op).hom s) = 0) :
    f.appTop.hom s = 0 := by

  let V : Y.affineOpens → X.Opens := fun U => f ⁻¹ᵁ U.1
  have hcover : (⊤ : X.Opens) ≤ iSup V := by
    intro x _
    obtain ⟨U, hU, hxU⟩ : ∃ U : Y.Opens, IsAffineOpen U ∧ f x ∈ U := by
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
      exact ⟨U, hU, hxU⟩
    exact Opens.mem_iSup.mpr ⟨⟨U, hU⟩, hxU⟩
  apply TopCat.Sheaf.eq_of_locally_eq' X.sheaf V ⊤ (fun U => homOfLE le_top) hcover
  intro U
  have hU := h U
  rw [app_res_top] at hU
  have h0 : (X.presheaf.map (homOfLE (le_top (a := f ⁻¹ᵁ U.1))).op).hom 0 = 0 := map_zero _
  exact hU.trans h0.symm

theorem ofIdealTop_le_ker (f : X ⟶ Y) (S : Set Γ(Y, ⊤)) (hS : ∀ s ∈ S, f.appTop.hom s = 0) :
    Scheme.IdealSheafData.ofIdealTop (Ideal.span S) ≤ f.ker := by
  rw [Scheme.Hom.ker, Scheme.IdealSheafData.le_ofIdeals_iff]
  intro U
  rw [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_le_iff_le_comap, Ideal.span_le]
  intro s hs
  rw [SetLike.mem_coe, Ideal.mem_comap, RingHom.mem_ker, app_res_top, hS s hs, map_zero]

theorem subschemeι_appTop_eq_zero (S : Set Γ(Y, ⊤)) (s : Γ(Y, ⊤)) (hs : s ∈ S) :
    (Scheme.IdealSheafData.ofIdealTop (Ideal.span S)).subschemeι.appTop.hom s = 0 := by
  set I := Scheme.IdealSheafData.ofIdealTop (X := Y) (Ideal.span S) with hI
  apply appTop_eq_zero_of_forall_app
  intro U
  have h1 : (Y.presheaf.map (homOfLE (le_top (a := U.1))).op).hom s ∈ I.ideal U := by
    rw [hI, Scheme.IdealSheafData.ofIdealTop_ideal]
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span hs)
  have h2 : I.ideal U ≤ RingHom.ker (I.subschemeι.app U.1).hom := by
    have h := Scheme.Hom.ideal_ker_le I.subschemeι U
    rwa [Scheme.IdealSheafData.ker_subschemeι] at h
  exact h2 h1

end Sections

section Main

theorem main
    (k : Type u) [Field k] [IsAlgClosed k] {Z : Scheme.{u}} (q : Z ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType q] (S : Set Γ(Z, ⊤))
    (e : Spec (CommRingCat.of k) ⟶ Z)
    (hart : ∀ {T : Scheme.{u}} [Subsingleton ↥T] (t : T ⟶ Spec (CommRingCat.of k))
      [LocallyOfFiniteType t] (x : T ⟶ Z), x ≫ q = t → (∀ s ∈ S, x.appTop.hom s = 0) → x = t ≫ e)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : T ⟶ Z) (hx : x ≫ q = t)
    (hs : ∀ s ∈ S, x.appTop.hom s = 0) : x = t ≫ e := by

  set I := Scheme.IdealSheafData.ofIdealTop (X := Z) (Ideal.span S) with hI
  let Z' : Scheme.{u} := I.subscheme
  let ι' : Z' ⟶ Z := I.subschemeι
  let q' : Z' ⟶ Spec (CommRingCat.of k) := ι' ≫ q
  have hι'S : ∀ s ∈ S, ι'.appTop.hom s = 0 := fun s hs => subschemeι_appTop_eq_zero S s hs
  haveI : JacobsonSpace Z' := LocallyOfFiniteType.jacobsonSpace q'

  have hclosed : ∀ z : Z', IsClosed ({z} : Set Z') → ι' z = e (IsLocalRing.closedPoint k) := by
    intro z hz
    let kz := pointOfClosedPoint q' z hz
    have h1 : (kz ≫ ι') ≫ q = 𝟙 _ := by
      rw [Category.assoc]; exact pointOfClosedPoint_comp q' z hz
    have h2 : ∀ s ∈ S, (kz ≫ ι').appTop.hom s = 0 := by
      intro s hs
      rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, hι'S s hs, map_zero]
    have h3 : kz ≫ ι' = 𝟙 _ ≫ e := hart (𝟙 _) (kz ≫ ι') h1 h2
    rw [Category.id_comp] at h3
    have h4 := congrArg (fun φ : Spec (CommRingCat.of k) ⟶ Z => φ (IsLocalRing.closedPoint k)) h3
    simp only [Scheme.Hom.comp_apply] at h4
    rwa [pointOfClosedPoint_apply] at h4

  haveI : Subsingleton ↥Z' := by
    constructor
    intro z₁ z₂
    have hinj : Function.Injective ι' := ι'.isClosedEmbedding.injective
    have hcp : ∀ c ∈ closedPoints Z', closedPoints Z' = {c} := by
      intro c hc
      ext z
      constructor
      · intro hz
        exact hinj ((hclosed z hz).trans (hclosed c hc).symm)
      · rintro rfl; exact hc
    have hz₁ : z₁ ∈ closure (closedPoints Z') := by rw [closure_closedPoints]; trivial
    have hz₂ : z₂ ∈ closure (closedPoints Z') := by rw [closure_closedPoints]; trivial
    have hne : (closedPoints Z').Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      rw [h, closure_empty] at hz₁
      exact hz₁
    obtain ⟨c, hc⟩ := hne
    rw [hcp c hc, (mem_closedPoints_iff.mp hc).closure_eq] at hz₁ hz₂
    rw [Set.mem_singleton_iff] at hz₁ hz₂
    rw [hz₁, hz₂]

  have hι' : ι' = q' ≫ e := hart q' ι' rfl hι'S

  have hker : ι'.ker ≤ x.ker := by
    show I.subschemeι.ker ≤ x.ker
    rw [Scheme.IdealSheafData.ker_subschemeι]
    exact ofIdealTop_le_ker x S hs
  let x' : T ⟶ Z' := IsClosedImmersion.lift ι' x hker
  have hx' : x' ≫ ι' = x := IsClosedImmersion.lift_fac _ _ _
  calc x = x' ≫ ι' := hx'.symm
    _ = x' ≫ q' ≫ e := by rw [← hι']
    _ = (x' ≫ ι') ≫ q ≫ e := by simp only [q', Category.assoc]
    _ = t ≫ e := by rw [hx', ← Category.assoc, hx]

end Main

end AlgebraicGeometry.ArtinianPointsDetect

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {Z : Scheme.{u}} (q : Z ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType q] (S : Set Γ(Z, ⊤))
    (e : Spec (CommRingCat.of k) ⟶ Z)
    (hart : ∀ {T : Scheme.{u}} [Subsingleton ↥T] (t : T ⟶ Spec (CommRingCat.of k))
      [LocallyOfFiniteType t] (x : T ⟶ Z), x ≫ q = t → (∀ s ∈ S, x.appTop.hom s = 0) → x = t ≫ e)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : T ⟶ Z) (hx : x ≫ q = t)
    (hs : ∀ s ∈ S, x.appTop.hom s = 0) : x = t ≫ e :=
  AlgebraicGeometry.ArtinianPointsDetect.main k q S e hart t x hx hs
end S_AlgebraicGeometry_eq_comp_of_forall_appTop_eq_zero_of_forall_subsingleton
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
