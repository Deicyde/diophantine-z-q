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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen.lean
  Source sha256  : d179a7d298150f3e934a2561558aa0b2fd46d7730f858474a0153af30b689b0b
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

namespace P2MW.S_AlgebraicGeometry_Scheme_finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry"

open scoped CategoryTheory.MonObj
r2nos_open_scoped_dual "CategoryTheory.MonObj"

noncomputable section

namespace P2mThetaFinB
r2nos_namespace_dual

variable {k : Type u} [Field k] {X : Scheme.{u}} {t : X ⟶ Spec (CommRingCat.of k)}

abbrev Pt (t : X ⟶ Spec (CommRingCat.of k)) := Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t

def pt (z : Pt t) : X := z.left (IsLocalRing.closedPoint k)

lemma left_comp (z : Pt t) : (z.left : Spec (CommRingCat.of k) ⟶ X) ≫ t = 𝟙 _ := Over.w z

lemma pt_injective [LocallyOfFiniteType t] [IsAlgClosed k] : Function.Injective (pt (t := t)) :=
  fun z z' h => Over.OverMorphism.ext
    (ext_of_apply_closedPoint_eq (X := X) (f := z.left) (g := z'.left) t (left_comp z)
      (left_comp z') h)

lemma exists_pt_eq [LocallyOfFiniteType t] [IsAlgClosed k] {y : X} (hy : IsClosed ({y} : Set X)) :
    ∃ z : Pt t, pt z = y :=
  ⟨Over.homMk (pointOfClosedPoint (X := X) t y hy) (by simp), pointOfClosedPoint_apply t y hy _⟩

section Grp

variable [GrpObj (Over.mk t)]

def lmul (z : Pt t) : Over.mk t ⟶ Over.mk t :=
  (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ z) * 𝟙 (Over.mk t)

lemma comp_lmul (x z : Pt t) : x ≫ lmul z = z * x := by
  have h1 : CartesianMonoidalCategory.toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≫ z = z := by
    rw [show CartesianMonoidalCategory.toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ from
      Subsingleton.elim _ _]
    exact Category.id_comp z
  rw [lmul, MonObj.comp_mul, Category.comp_id, ← Category.assoc,
    CartesianMonoidalCategory.comp_toUnit, h1]

lemma pt_mul (z x : Pt t) : pt (z * x) = (lmul z).left (pt x) := by
  rw [← comp_lmul]
  rfl

def invLeft (t : X ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk t)] : X ⟶ X :=
  (ι[Over.mk t]).left

lemma pt_inv (x : Pt t) : pt x⁻¹ = invLeft t (pt x) := by
  rw [Hom.inv_def]
  rfl

def Cplus (t : X ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk t)] (Z : Set X) : Set X :=
  ⋂ z ∈ {z : Pt t | pt z ∈ Z}, ((lmul z).left : X ⟶ X) ⁻¹' Z

lemma isClosed_Cplus {Z : Set X} (hZ : IsClosed Z) : IsClosed (Cplus t Z) :=
  isClosed_biInter fun z _ => hZ.preimage (lmul z).left.continuous

lemma mem_Cplus_iff {Z : Set X} (x : Pt t) :
    pt x ∈ Cplus t Z ↔ ∀ z : Pt t, pt z ∈ Z → pt (z * x) ∈ Z := by
  simp only [Cplus, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_preimage, pt_mul]

def C (t : X ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk t)] (Z : Set X) : Set X :=
  Cplus t Z ∩ (invLeft t) ⁻¹' Cplus t Z

lemma isClosed_C {Z : Set X} (hZ : IsClosed Z) : IsClosed (C t Z) :=
  (isClosed_Cplus hZ).inter ((isClosed_Cplus hZ).preimage (invLeft t).continuous)

lemma mem_stab_iff {Z : Set X} (x : Pt t) :
    (∀ z : Pt t, pt z ∈ Z ↔ pt (z * x) ∈ Z) ↔ pt x ∈ C t Z := by
  rw [C, Set.mem_inter_iff, Set.mem_preimage, ← pt_inv, mem_Cplus_iff, mem_Cplus_iff]
  constructor
  · intro h
    refine ⟨fun z hz => (h z).1 hz, fun z hz => ?_⟩
    have := (h (z * x⁻¹)).2
    rw [inv_mul_cancel_right] at this
    exact this hz
  · rintro ⟨h₁, h₂⟩ z
    refine ⟨h₁ z, fun hz => ?_⟩
    have := h₂ (z * x) hz
    rwa [mul_inv_cancel_right] at this

end Grp

variable (t) in

lemma finite_of_isClosed_of_subset_affineOpen [IsProper t] {C : Set X} (hC : IsClosed C)
    {U : X.Opens} (hU : IsAffineOpen U) (hCU : C ⊆ U) : C.Finite := by

  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨C, hC⟩
  have hrange : Set.range I.subschemeι = C := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    exact Scheme.IdealSheafData.coe_support_vanishingIdeal ⟨C, hC⟩

  have htop : I.subschemeι ⁻¹ᵁ U = ⊤ := by
    ext y
    simp only [TopologicalSpace.Opens.map_coe, Set.mem_preimage, SetLike.mem_coe,
      TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    exact hCU (hrange ▸ Set.mem_range_self y)
  have hAff : IsAffine I.subscheme := by
    have h1 : IsAffineOpen (I.subschemeι ⁻¹ᵁ U) := hU.preimage I.subschemeι
    rw [htop] at h1
    haveI : IsAffine (⊤ : I.subscheme.Opens) := h1
    exact IsAffine.of_isIso I.subscheme.topIso.inv

  have hfin : IsFinite (I.subschemeι ≫ t) := by
    rw [IsFinite.iff_isProper_and_isAffineHom]
    exact ⟨inferInstance, isAffineHom_of_isAffine _⟩

  have huniv : (Set.univ : Set I.subscheme).Finite := by
    have := (I.subschemeι ≫ t).finite_preimage_singleton (IsLocalRing.closedPoint k)
    refine this.subset fun y _ => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact Subsingleton.elim _ _
  rw [← hrange, ← Set.image_univ]
  exact huniv.image _

theorem main [IsAlgClosed k] [IsProper t] [GrpObj (Over.mk t)] (Z : Set X) (hZ : IsClosed Z) (U : X.Opens)
    (hU : IsAffineOpen U) (hZU : Zᶜ ⊆ U) (he : pt (1 : Pt t) ∉ Z) :
    Set.Finite {x : Pt t | ∀ z : Pt t, pt z ∈ Z ↔ pt (z * x) ∈ Z} := by
  have hJ : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace t

  have hS : {x : Pt t | ∀ z : Pt t, pt z ∈ Z ↔ pt (z * x) ∈ Z} = pt ⁻¹' C t Z := by
    ext x
    exact mem_stab_iff x
  rw [hS]

  have hCZ : C t Z ⊆ U := by
    intro y hy
    by_contra hyU
    have hyZ : y ∈ Z := by
      by_contra hyZ
      exact hyU (hZU hyZ)
    have hcl : IsClosed (C t Z ∩ Z) := (isClosed_C hZ).inter hZ
    have hne : (C t Z ∩ Z ∩ closedPoints X).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have := JacobsonSpace.closure_inter_closedPoints_eq_closure hcl.isLocallyClosed
      rw [hemp, closure_empty, hcl.closure_eq] at this
      exact (this ▸ (Set.mem_empty_iff_false y)).mp ⟨hy, hyZ⟩
    obtain ⟨y₀, ⟨hy₀C, hy₀Z⟩, hy₀cl⟩ := hne
    obtain ⟨z₀, rfl⟩ := exists_pt_eq (t := t) (mem_closedPoints_iff.mp hy₀cl)
    have hst := (mem_stab_iff z₀).2 hy₀C 1
    rw [one_mul] at hst
    exact he (hst.2 hy₀Z)
  have hCfin : (C t Z).Finite := finite_of_isClosed_of_subset_affineOpen t (isClosed_C hZ) hU hCZ
  exact hCfin.preimage pt_injective.injOn

end P2mThetaFinB

end

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [IsProper t] [GrpObj (Over.mk t)]
    (Z : Set X) (hZ : IsClosed Z) (U : X.Opens) (hU : IsAffineOpen U) (hZU : Zᶜ ⊆ (U : Set X))
    (he : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t).left (IsLocalRing.closedPoint k) ∉ Z) :
    Set.Finite {x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t |
      ∀ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
        z.left (IsLocalRing.closedPoint k) ∈ Z ↔ (z * x).left (IsLocalRing.closedPoint k) ∈ Z} :=
  P2mThetaFinB.main Z hZ U hU hZU he
end S_AlgebraicGeometry_Scheme_finite_setOf_forall_mem_iff_mul_mem_of_isClosed_of_compl_subset_of_isAffineOpen
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
