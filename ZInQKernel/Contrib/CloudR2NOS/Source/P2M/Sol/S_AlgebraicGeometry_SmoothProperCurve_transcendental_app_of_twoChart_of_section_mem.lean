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
  Source file    : P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_transcendental_app_of_twoChart_of_section_mem.lean
  Source sha256  : 666a8dbda40f9af1b9e251b809a645d115815628b7851a94358ea6f69fbc3fac
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 4 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 5 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: T6×1; rule citations in the batch ledger.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_section
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_transcendental_app_of_twoChart_of_section_mem
r2nos_namespace_dual

set_option autoImplicit false

universe u

open scoped TensorProduct
r2nos_open_scoped_dual "TensorProduct"
open Polynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
r2nos_open_dual "Polynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry"

namespace ORDERTRANSC
r2nos_namespace_dual

theorem zero_or_isUnit_of_isAlgebraic {K D : Type u} [Field K] [CommRing D] [IsDomain D] [Algebra K D]
    (a : D) (h : IsAlgebraic K a) : a = 0 ∨ IsUnit a := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · exact Or.inr ((isAlgebraic_iff_isIntegral.mp h).isUnit ha)

theorem zero_or_isUnit_of_isField {D : Type u} [CommRing D] (hD : IsField D) (a : D) : a = 0 ∨ IsUnit a := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · obtain ⟨b, hb⟩ := hD.mul_inv_cancel ha
    exact Or.inr ⟨⟨a, b, hb, by rw [mul_comm]; exact hb⟩, rfl⟩

theorem exists_mem_fibre_not_mem_range
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (y : Spec (CommRingCat.of R)) :
    ∃ u : C, c.base u = y ∧ u ∉ Set.range ε.1.base := by

  let F := c.fiber y
  let ι := c.fiberι y
  let q := c.fiberToSpecResidueField y
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI hsrd : SmoothOfRelativeDimension 1 q := by
    show SmoothOfRelativeDimension 1 (pullback.snd _ _)
    exact MorphismProperty.pullback_snd _ _ inferInstance
  let p : Spec ((Spec (CommRingCat.of R)).residueField y) ⟶ F :=
    pullback.lift ((Spec (CommRingCat.of R)).fromSpecResidueField y ≫ ε.1) (𝟙 _)
      (by rw [Category.assoc, ε.2, Category.comp_id, Category.id_comp])
  have hp : p ≫ q = 𝟙 _ := pullback.lift_snd _ _ _
  have hpι : p ≫ ι = (Spec (CommRingCat.of R)).fromSpecResidueField y ≫ ε.1 := pullback.lift_fst _ _ _

  let x₀ : F := p.base (IsLocalRing.closedPoint ((Spec (CommRingCat.of R)).residueField y))
  haveI hdvr : IsDiscreteValuationRing (F.presheaf.stalk x₀) :=
    @AlgebraicGeometry.SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_section _ _ F q
      inferInstance hsrd p hp

  let S := F.presheaf.stalk x₀
  let η : Spec (F.presheaf.stalk x₀) := ⟨⊥, Ideal.isPrime_bot⟩
  have hη : η ≠ IsLocalRing.closedPoint S := by
    intro h
    have := congrArg PrimeSpectrum.asIdeal h
    exact IsDiscreteValuationRing.not_a_field S this.symm
  let u' : F := (F.fromSpecStalk x₀).base η
  have hu' : u' ≠ x₀ := by
    intro h
    apply hη
    apply (F.fromSpecStalk x₀).isEmbedding.injective
    change (F.fromSpecStalk x₀).base η = (F.fromSpecStalk x₀).base (IsLocalRing.closedPoint S)
    erw [Scheme.fromSpecStalk_closedPoint]
    exact h

  refine ⟨ι.base u', ?_, ?_⟩
  · have : ι.base u' ∈ Set.range (c.fiberι y).base := ⟨u', rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this
  · rintro ⟨y', hy'⟩

    have hcε : ∀ z, c.base (ε.1.base z) = z := fun z => by
      have := Scheme.Hom.comp_apply ε.1 c z
      rw [ε.2] at this
      exact this.symm
    have hyy : y' = y := by
      have h1 := hcε y'
      rw [hy'] at h1
      have : ι.base u' ∈ Set.range (c.fiberι y).base := ⟨u', rfl⟩
      rw [Scheme.Hom.range_fiberι] at this
      rw [← h1]; exact this
    subst hyy
    apply hu'
    apply ι.isEmbedding.injective
    rw [← hy']
    show _ = ι.base (p.base _)
    rw [← Scheme.Hom.comp_apply, hpι, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

theorem main
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U V : C.Opens) (hUV : U ⊔ V = ⊤)
    (hUε : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base) (hεV : ∀ x ∈ Set.range ε.1.base, x ∈ V)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hf : U ⊓ V = C.basicOpen f) (hg : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (K : Type u) [Field K] [Algebra R K] :
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
        ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)) ⁻¹ᵁ U);
      Transcendental K (((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)).app U).hom f)) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
        ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)) ⁻¹ᵁ V);
      Transcendental K (((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)).app V).hom g)) := by

  let sK := Scheme.TwoAffineOpenCover.specMap R K
  let CK := pullback c sK
  let π : CK ⟶ C := pullback.fst c sK
  let σ : CK ⟶ Spec (CommRingCat.of K) := pullback.snd c sK
  let UK : CK.Opens := π ⁻¹ᵁ U
  let VK : CK.Opens := π ⁻¹ᵁ V
  let fK : Γ(CK, UK) := (π.app U).hom f
  let gK : Γ(CK, VK) := (π.app V).hom g

  let t : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  let y : Spec (CommRingCat.of R) := sK.base t
  haveI : IsIntegral CK :=
    pullback_of_geometrically (GeometricallyIntegral.geometrically_isIntegral (f := c)) K sK
  have hUVf : UK ⊓ VK = CK.basicOpen fK := by
    show π ⁻¹ᵁ U ⊓ π ⁻¹ᵁ V = CK.basicOpen ((π.app U).hom f)
    rw [← Scheme.preimage_basicOpen, ← hf]; rfl
  have hUVg : UK ⊓ VK = CK.basicOpen gK := by
    show π ⁻¹ᵁ U ⊓ π ⁻¹ᵁ V = CK.basicOpen ((π.app V).hom g)
    rw [← Scheme.preimage_basicOpen, ← hg]; rfl
  have hcov : UK ⊔ VK = ⊤ := by
    show π ⁻¹ᵁ U ⊔ π ⁻¹ᵁ V = ⊤
    rw [← Scheme.Hom.preimage_sup, hUV]; rfl

  obtain ⟨u, hcu, hur⟩ := exists_mem_fibre_not_mem_range c ε y
  have huU : u ∈ U := (hUε u).mpr hur
  obtain ⟨zU, hzU, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := c) (g := sK) u t hcu
  have hzU' : zU ∈ UK := by
    show π.base zU ∈ U
    change (pullback.fst c sK).base zU = u at hzU
    rw [hzU]; exact huU

  have hcε : ∀ z, c.base (ε.1.base z) = z := fun z => by
    have := Scheme.Hom.comp_apply ε.1 c z
    rw [ε.2] at this
    exact this.symm
  obtain ⟨zV, hzV, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := c) (g := sK) (ε.1.base y) t (hcε y)
  have hzV' : zV ∈ VK := by
    show π.base zV ∈ V
    change (pullback.fst c sK).base zV = ε.1.base y at hzV
    rw [hzV]; exact hεV _ ⟨y, rfl⟩
  have hzVU : zV ∉ UK := by
    show π.base zV ∉ U
    change (pullback.fst c sK).base zV = ε.1.base y at hzV
    rw [hzV]; exact fun h => (hUε _).mp h ⟨y, rfl⟩

  have hirr := (IrreducibleSpace.isIrreducible_univ CK).isPreirreducible
  have not_disjoint : UK ⊓ VK ≠ ⊥ := by
    intro hbot
    obtain ⟨w, -, hwU, hwV⟩ := hirr _ _ UK.isOpen VK.isOpen ⟨zU, trivial, hzU'⟩ ⟨zV, trivial, hzV'⟩
    have hw : w ∈ UK ⊓ VK := ⟨hwU, hwV⟩
    rw [hbot] at hw
    exact hw
  have not_VK_le_UK : ¬ (VK ≤ UK) := fun h => hzVU (h hzV')
  haveI : Nonempty UK := ⟨⟨zU, hzU'⟩⟩
  haveI : Nonempty VK := ⟨⟨zV, hzV'⟩⟩
  haveI : IsDomain Γ(CK, UK) := IsIntegral.component_integral UK
  haveI : IsDomain Γ(CK, VK) := IsIntegral.component_integral VK

  have hg_cases : ¬ (gK = 0 ∨ IsUnit gK) := by
    rintro (h0 | hunit)
    · apply not_disjoint
      rw [hUVg, h0]
      exact Scheme.basicOpen_zero _ _
    · apply not_VK_le_UK
      have hb : CK.basicOpen gK = VK := Scheme.basicOpen_of_isUnit _ hunit
      intro w hw
      have : w ∈ UK ⊓ VK := by rw [hUVg, hb]; exact hw
      exact this.1
  refine ⟨?_, ?_⟩
  ·
    letI := Scheme.TwoAffineOpenCover.algebraOfHom σ UK
    intro halg
    rcases zero_or_isUnit_of_isAlgebraic fK halg with h0 | hunit
    · apply not_disjoint
      rw [hUVf, h0]
      exact Scheme.basicOpen_zero _ _
    · have hb : CK.basicOpen fK = UK := Scheme.basicOpen_of_isUnit _ hunit
      have hle : UK ≤ VK := by
        intro w hw
        have : w ∈ UK ⊓ VK := by rw [hUVf, hb]; exact hw
        exact this.2
      have htop : VK = ⊤ := by
        apply top_le_iff.mp
        rw [← hcov]
        exact sup_le hle le_rfl

      have hF : IsField Γ(CK, ⊤) := isField_of_universallyClosed (f := σ)
      let e : Γ(CK, ⊤) ≃+* Γ(CK, VK) :=
        (CK.presheaf.mapIso (eqToIso htop).op).commRingCatIsoToRingEquiv
      have hFV : IsField Γ(CK, VK) := MulEquiv.isField hF e.symm.toMulEquiv
      exact hg_cases (zero_or_isUnit_of_isField hFV gK)
  ·
    letI := Scheme.TwoAffineOpenCover.algebraOfHom σ VK
    intro halg
    exact hg_cases (zero_or_isUnit_of_isAlgebraic gK halg)

end ORDERTRANSC

open scoped TensorProduct in
r2nos_open_scoped_dual "TensorProduct" in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra _root_.AlgebraicGeometry in
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve NeronModelInfra" in

theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U V : C.Opens) (hUV : U ⊔ V = ⊤)
    (hUε : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base) (hεV : ∀ x ∈ Set.range ε.1.base, x ∈ V)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hf : U ⊓ V = C.basicOpen f) (hg : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1) :
    (∀ (K : Type u) [Field K] [Algebra R K],
        letI := Scheme.TwoAffineOpenCover.algebraOfHom
          (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
          ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)) ⁻¹ᵁ U);
        Transcendental K (((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)).app U).hom f)) ∧
      (∀ (K : Type u) [Field K] [Algebra R K],
        letI := Scheme.TwoAffineOpenCover.algebraOfHom
          (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
          ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)) ⁻¹ᵁ V);
        Transcendental K (((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)).app V).hom g)) :=
  ⟨fun K _ _ => (ORDERTRANSC.main R c ε U V hUV hUε hεV f g hf hg hfg K).1,
   fun K _ _ => (ORDERTRANSC.main R c ε U V hUV hUε hεV f g hf hg hfg K).2⟩
end S_AlgebraicGeometry_SmoothProperCurve_transcendental_app_of_twoChart_of_section_mem
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
