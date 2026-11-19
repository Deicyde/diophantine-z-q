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
  Source file    : P2M/Sol/S_AlgebraicCurve_exists_closedPoint_range_stalk_eq.lean
  Source sha256  : 0f565ee56aa68fcfda9c70e8a583b58592920e3959d3cfba0a77ec2c9ec630af
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 3 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 5 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v2 (lane C4 drift rules v2 ⊇ v1), applied: T1v2×2; rule citations in the batch ledger.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_valuationRing_stalk_of_smoothOfRelativeDimension_one
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_isClosed_singleton_of_ne_genericPoint
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicCurve_exists_closedPoint_range_stalk_eq
r2nos_namespace_dual

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing Topology
r2nos_open_dual "CategoryTheory AlgebraicGeometry IsLocalRing Topology"

namespace AlgebraicCurve
r2nos_namespace_dual
w03_export "AlgebraicCurve" "Place baseToFunctionField isClosed_singleton_of_ne_genericPoint"
w03_open "AlgebraicCurve"

theorem exists_lift_of_valuationSubring
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c]
    (R : ValuationSubring C.functionField) (hK : ∀ a : K, baseToFunctionField c a ∈ R) :
    ∃ ℓ : Spec (CommRingCat.of R) ⟶ C,
      Spec.map (CommRingCat.ofHom (algebraMap R C.functionField)) ≫ ℓ =
        C.fromSpecStalk (genericPoint C) ∧
      ℓ ≫ c = Spec.map (CommRingCat.ofHom ((baseToFunctionField c).codRestrict R hK)) := by
  classical
  set η := genericPoint C with hη
  let A : CommRingCat.of R ⟶ C.presheaf.stalk η :=
    CommRingCat.ofHom (algebraMap R C.functionField)
  let B : CommRingCat.of K ⟶ CommRingCat.of R :=
    CommRingCat.ofHom ((baseToFunctionField c).codRestrict R hK)
  have hBA : B ≫ A = (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ c.appTop ≫
      C.presheaf.germ ⊤ η trivial := by
    ext a
    rfl

  have w : C.fromSpecStalk η ≫ c = Spec.map A ≫ Spec.map B := by
    apply ext_of_isAffine
    rw [← Spec.map_comp, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
    have h1 : (homOfLE (le_top : (⊤ : (Spec (C.presheaf.stalk η)).Opens) ≤ ⊤)).op = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [h1, CategoryTheory.Functor.map_id, Category.comp_id]

    have h2 : (Spec.map (B ≫ A)).appTop =
        (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ (B ≫ A) ≫
          (Scheme.ΓSpecIso (C.presheaf.stalk η)).inv := by
      rw [← Iso.inv_comp_eq]
      exact (Scheme.ΓSpecIso_inv_naturality (B ≫ A)).symm
    rw [h2, hBA]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

  have hvc : ValuativeCriterion c := by
    have h : IsProper c := inferInstance
    rw [IsProper.eq_valuativeCriterion] at h
    exact h.1.1.1
  obtain ⟨ℓ, hl₁, hl₂⟩ := (hvc.existence ⟨R, C.functionField, C.fromSpecStalk η, Spec.map B, ⟨w⟩⟩).exists_lift
  dsimp only at hl₁ hl₂
  exact ⟨ℓ, hl₁, hl₂⟩

private theorem _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.ValuationSubring.eq_of_le_of_isUnit_imp {F : Type*} [Field F]
    {S R : ValuationSubring F} (hle : S ≤ R)
    (hunit : ∀ s : S, IsUnit (⟨(s : F), hle s.2⟩ : R) → IsUnit s) : S = R := by
  refine le_antisymm hle fun r hr => ?_
  by_contra hrS
  have hr0 : r ≠ 0 := by rintro rfl; exact hrS S.zero_mem
  have hinv : r⁻¹ ∈ S := (S.mem_or_inv_mem r).resolve_left hrS
  have hu : IsUnit (⟨r⁻¹, hle hinv⟩ : R) :=
    isUnit_iff_exists_inv.mpr ⟨⟨r, hr⟩, Subtype.ext (inv_mul_cancel₀ hr0)⟩
  obtain ⟨w, hw⟩ := hunit ⟨r⁻¹, hinv⟩ hu

  have : ((w⁻¹ : Sˣ) : S).1 = r := by
    have h1 : ((w⁻¹ : Sˣ) : S).1 * r⁻¹ = 1 := by
      have := congrArg (fun t : S => t.1) (w.inv_mul)
      simpa [hw] using this
    field_simp at h1
    linear_combination h1
  exact hrS (this ▸ ((w⁻¹ : Sˣ) : S).2)

r2nos_alias "P2MW.S_AlgebraicCurve_exists_closedPoint_range_stalk_eq.ValuationSubring.eq_of_le_of_isUnit_imp" "ValuationSubring.eq_of_le_of_isUnit_imp"
end AlgebraicCurve

open _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicCurve _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicCurve_exists_closedPoint_range_stalk_eq.AlgebraicCurve in
r2nos_open_dual "_root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicCurve _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicCurve_exists_closedPoint_range_stalk_eq.AlgebraicCurve" in

theorem solution
    {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c] :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∀ v : AlgebraicCurve.Place K C.functionField, ∃ x : C, IsClosed ({x} : Set C) ∧
      (algebraMap (C.presheaf.stalk x) C.functionField).range = v.toValuationSubring.toSubring := by
  letI := (baseToFunctionField c).toAlgebra
  intro v
  classical
  set R := v.toValuationSubring with hRdef
  have hK : ∀ a : K, baseToFunctionField c a ∈ R := v.algebraMap_mem'
  obtain ⟨ℓ, hl₁, -⟩ := exists_lift_of_valuationSubring c R hK
  set x := ℓ.base (closedPoint R) with hxdef
  have hgen : genericPoint C ⤳ x := (genericPoint_spec C).specializes trivial

  set φ := Scheme.stalkClosedPointTo ℓ with hφdef
  have hφ : φ ≫ CommRingCat.ofHom (algebraMap R C.functionField) =
      C.presheaf.stalkSpecializes hgen := by
    apply Spec.map_injective
    rw [← cancel_mono (C.fromSpecStalk x), Spec.map_comp, Category.assoc,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl₁, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  have hφ' : ∀ s, algebraMap R C.functionField (φ.hom s) =
      algebraMap (C.presheaf.stalk x) C.functionField s := by
    intro s
    have := congrArg (fun g => g.hom s) hφ
    simp at this
    exact this

  haveI : ValuationRing (C.presheaf.stalk x) :=
    AlgebraicGeometry.valuationRing_stalk_of_smoothOfRelativeDimension_one c x
  let S : ValuationSubring C.functionField :=
    (ValuationRing.valuation (C.presheaf.stalk x) C.functionField).valuationSubring
  have hS : ∀ f, f ∈ S ↔ ∃ a, algebraMap (C.presheaf.stalk x) C.functionField a = f := fun f =>
    ValuationRing.mem_integer_iff (C.presheaf.stalk x) C.functionField f
  have hSR : S ≤ R := by
    intro f hf
    obtain ⟨a, rfl⟩ := (hS f).mp hf
    rw [← hφ' a]
    exact (φ.hom a).2
  let ψ : C.presheaf.stalk x →+* S :=
    (algebraMap (C.presheaf.stalk x) C.functionField).codRestrict S fun a => (hS _).mpr ⟨a, rfl⟩
  have hunit : ∀ s : S, IsUnit (⟨(s : C.functionField), hSR s.2⟩ : R) → IsUnit s := by
    rintro ⟨f, hf⟩ hu
    obtain ⟨a, rfl⟩ := (hS f).mp hf
    have hu' : IsUnit (φ.hom a) := by
      have heq : φ.hom a = ⟨algebraMap (C.presheaf.stalk x) C.functionField a, hSR hf⟩ :=
        Subtype.ext (hφ' a)
      rwa [heq]
    have ha : IsUnit a := isUnit_of_map_unit φ.hom a hu'
    exact ha.map ψ
  have hSReq : S = R := ValuationSubring.eq_of_le_of_isUnit_imp hSR hunit
  have hrange : (algebraMap (C.presheaf.stalk x) C.functionField).range = R.toSubring := by
    rw [← hSReq]
    ext f
    rw [RingHom.mem_range]
    exact (hS f).symm

  have key : ∀ y : C, y = genericPoint C →
      (algebraMap (C.presheaf.stalk y) C.functionField).range = ⊤ := by
    rintro y rfl
    refine eq_top_iff.mpr fun f _ => ⟨f, ?_⟩
    change (C.presheaf.stalkSpecializes (specializes_refl _)).hom f = f
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  have hxη : x ≠ genericPoint C := by
    intro hx
    apply v.ne_top'
    apply ValuationSubring.toSubring_injective
    change R.toSubring = _
    rw [← hrange, key x hx]
    rfl
  exact ⟨x, isClosed_singleton_of_ne_genericPoint c x hxη, hrange⟩
end S_AlgebraicCurve_exists_closedPoint_range_stalk_eq
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
