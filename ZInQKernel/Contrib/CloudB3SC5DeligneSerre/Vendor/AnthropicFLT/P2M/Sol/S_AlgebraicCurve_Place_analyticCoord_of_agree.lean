/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_analyticCoord_of_agree (git blob dab4891a172c18e3b870693659868dde8bf4e164, sha256 b1a2b6d136ee09f7a766d481f68a330bab4f176ef410ae707a336318d8d9bef9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_mem_of_ord_nonneg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve.Place
end AlgebraicCurve.Place

namespace P2MW.S_AlgebraicCurve_Place_analyticCoord_of_agree

set_option autoImplicit false

open AlgebraicCurve
open scoped Manifold ContDiff

namespace AnalyticCoordAgree

open _root_.AlgebraicCurve.Place

theorem evalAt_sub_algebraMap {F : Type*} [Field F] [Algebra ℂ F]
    (v : Place ℂ F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) (c : ℂ) :
    v.evalAt (f - algebraMap ℂ F c) = v.evalAt f - c := by
  have hcm : algebraMap ℂ F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hmem : f - algebraMap ℂ F c ∈ v.toValuationSubring := sub_mem hf hcm
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv hmem, v.algebraMap_evalAt hv hf]
  have hsub : (⟨f - algebraMap ℂ F c, hmem⟩ : v.toValuationSubring)
      = ⟨f, hf⟩ - ⟨algebraMap ℂ F c, hcm⟩ := rfl
  rw [hsub, map_sub]
  congr 1

theorem isOpen_setOf_mem_toValuationSubring {F : Type*} [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] [TopologicalSpace (Place ℂ F)] [T2Space (Place ℂ F)]
    {f : F} (hf0 : f ≠ 0) :
    IsOpen {P : Place ℂ F | f ∈ P.toValuationSubring} := by
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := ℂ) f hf0
  have hsub : {P : Place ℂ F | f ∉ P.toValuationSubring} ⊆ ↑D.support := by
    intro P hP
    simp only [Finset.mem_coe, Finsupp.mem_support_iff, hD P]
    intro h0
    exact hP (P.mem_of_ord_nonneg hf0 (le_of_eq h0.symm))
  have hcl : IsClosed {P : Place ℂ F | f ∉ P.toValuationSubring} :=
    (Set.Finite.subset D.support.finite_toSet hsub).isClosed
  have : {P : Place ℂ F | f ∈ P.toValuationSubring}
      = {P : Place ℂ F | f ∉ P.toValuationSubring}ᶜ := by
    ext P; simp
  rw [this]
  exact hcl.isOpen_compl

theorem finite_setOf_evalAt_eq {F : Type*} [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] (hrat : ∀ P : Place ℂ F, P.IsRational)
    {f : F} (hf : Transcendental ℂ f) (t : ℂ) :
    {P : Place ℂ F | f ∈ P.toValuationSubring ∧ P.evalAt f = t}.Finite := by
  have hft : f - algebraMap ℂ F t ≠ 0 := by
    intro h
    exact hf (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap t)
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := ℂ) _ hft
  refine Set.Finite.subset D.support.finite_toSet ?_
  rintro P ⟨hmem, hval⟩
  simp only [Finset.mem_coe, Finsupp.mem_support_iff, hD P]
  intro h0
  have h1 : P.evalAt (f - algebraMap ℂ F t) = 0 := by
    rw [evalAt_sub_algebraMap P (hrat P) hmem, hval, sub_self]
  exact P.evalAt_ne_zero_of_ord_eq_zero (hrat P) hft h0 h1

theorem read_center_eq {F : Type*} [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    (P : Place ℂ F) (f : F) :
    Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm (extChartAt 𝓘(ℂ, ℂ) P P)) f
      = P.evalAt f := by
  rw [extChartAt_to_inv]

theorem read_sub_eventuallyEq {F : Type*} [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [T2Space (Place ℂ F)] (hrat : ∀ P : Place ℂ F, P.IsRational)
    (P : Place ℂ F) {f : F} (hf0 : f ≠ 0) (hfP : f ∈ P.toValuationSubring) (c : ℂ) :
    (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) (f - algebraMap ℂ F c))
      =ᶠ[nhds (extChartAt 𝓘(ℂ, ℂ) P P)]
    (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f - c) := by
  have hopen := isOpen_setOf_mem_toValuationSubring (F := F) hf0
  have hcont : ContinuousAt (extChartAt 𝓘(ℂ, ℂ) P).symm (extChartAt 𝓘(ℂ, ℂ) P P) :=
    continuousAt_extChartAt_symm P
  have hmemP : (extChartAt 𝓘(ℂ, ℂ) P).symm (extChartAt 𝓘(ℂ, ℂ) P P)
      ∈ {Q : Place ℂ F | f ∈ Q.toValuationSubring} := by
    rw [extChartAt_to_inv]; exact hfP
  have hev : ∀ᶠ z in nhds (extChartAt 𝓘(ℂ, ℂ) P P),
      (extChartAt 𝓘(ℂ, ℂ) P).symm z ∈ {Q : Place ℂ F | f ∈ Q.toValuationSubring} :=
    hcont.eventually_mem (hopen.mem_nhds hmemP)
  filter_upwards [hev] with z hz
  exact evalAt_sub_algebraMap _ (hrat _) hz c

theorem exists_hasStrictDerivAt_read {F : Type*} [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [T2Space (Place ℂ F)]
    (hF : ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ))
    (hrat : ∀ P : Place ℂ F, P.IsRational)
    (P : Place ℂ F) {f : F} (hf : Transcendental ℂ f) (hfP : f ∈ P.toValuationSubring)
    (hord : P.ord (f - algebraMap ℂ F (P.evalAt f)) = 1) :
    ∃ d : ℂ, d ≠ 0 ∧ HasStrictDerivAt
      (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f) d
      (extChartAt 𝓘(ℂ, ℂ) P P) := by
  have hf0 : f ≠ 0 := fun h => hf (h ▸ isAlgebraic_zero)
  have hg0 : f - algebraMap ℂ F (P.evalAt f) ≠ 0 := by
    intro h
    exact hf (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap _)
  obtain ⟨hmer, horder⟩ := hF _ hg0 P
  have h1 : meromorphicOrderAt
      (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z)
        (f - algebraMap ℂ F (P.evalAt f)))
      (extChartAt 𝓘(ℂ, ℂ) P P) = ((1 : ℤ) : WithTop ℤ) := by
    rw [horder, hord]
  obtain ⟨g, hgan, hgne, hgeq⟩ := (meromorphicOrderAt_eq_int_iff hmer).mp h1
  have hstrict : HasStrictDerivAt
      (fun z : ℂ => P.evalAt f + (z - extChartAt 𝓘(ℂ, ℂ) P P) * g z)
      (g (extChartAt 𝓘(ℂ, ℂ) P P)) (extChartAt 𝓘(ℂ, ℂ) P P) := by
    have hid : HasStrictDerivAt (fun z : ℂ => z - extChartAt 𝓘(ℂ, ℂ) P P) (1 - 0)
        (extChartAt 𝓘(ℂ, ℂ) P P) :=
      (hasStrictDerivAt_id _).sub (hasStrictDerivAt_const _ _)
    have hmul := hid.mul hgan.hasStrictDerivAt
    have := hmul.const_add (P.evalAt f)
    simpa using this
  have hB5 := read_sub_eventuallyEq (F := F) hrat P hf0 hfP (P.evalAt f)
  have hval : Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm (extChartAt 𝓘(ℂ, ℂ) P P)) f
      = P.evalAt f := read_center_eq P f
  have heq : (fun z : ℂ => P.evalAt f + (z - extChartAt 𝓘(ℂ, ℂ) P P) * g z)
      =ᶠ[nhds (extChartAt 𝓘(ℂ, ℂ) P P)]
      (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f) := by
    have hne : (fun z : ℂ => P.evalAt f + (z - extChartAt 𝓘(ℂ, ℂ) P P) * g z)
        =ᶠ[nhdsWithin (extChartAt 𝓘(ℂ, ℂ) P P) {extChartAt 𝓘(ℂ, ℂ) P P}ᶜ]
        (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f) := by
      filter_upwards [hgeq, hB5.filter_mono nhdsWithin_le_nhds] with z h2 h3
      have h4 : Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f - P.evalAt f
          = (z - extChartAt 𝓘(ℂ, ℂ) P P) * g z := by
        rw [← h3, h2]
        simp [smul_eq_mul]
      linear_combination -h4
    refine eventuallyEq_nhds_of_eventuallyEq_nhdsNE hne ?_
    simp
  exact ⟨g (extChartAt 𝓘(ℂ, ℂ) P P), hgne, hstrict.congr_of_eventuallyEq heq⟩

theorem analyticAt_read_of_ord_eq_one {F : Type*} [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [T2Space (Place ℂ F)]
    (hF : ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ))
    (hrat : ∀ P : Place ℂ F, P.IsRational)
    (P : Place ℂ F) {f : F} (hf : Transcendental ℂ f) (hfP : f ∈ P.toValuationSubring)
    (hord : P.ord (f - algebraMap ℂ F (P.evalAt f)) = 1) :
    AnalyticAt ℂ (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f)
      (extChartAt 𝓘(ℂ, ℂ) P P) ∧
    deriv (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f)
      (extChartAt 𝓘(ℂ, ℂ) P P) ≠ 0 := by
  have hf0 : f ≠ 0 := fun h => hf (h ▸ isAlgebraic_zero)
  have hg0 : f - algebraMap ℂ F (P.evalAt f) ≠ 0 := by
    intro h
    exact hf (sub_eq_zero.mp h ▸ isAlgebraic_algebraMap _)
  obtain ⟨hmer, horder⟩ := hF _ hg0 P
  have h1 : meromorphicOrderAt
      (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z)
        (f - algebraMap ℂ F (P.evalAt f)))
      (extChartAt 𝓘(ℂ, ℂ) P P) = ((1 : ℤ) : WithTop ℤ) := by
    rw [horder, hord]
  obtain ⟨g, hgan, hgne, hgeq⟩ := (meromorphicOrderAt_eq_int_iff hmer).mp h1
  have hB5 := read_sub_eventuallyEq (F := F) hrat P hf0 hfP (P.evalAt f)
  have heq : (fun z : ℂ => P.evalAt f + (z - extChartAt 𝓘(ℂ, ℂ) P P) * g z)
      =ᶠ[nhds (extChartAt 𝓘(ℂ, ℂ) P P)]
      (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f) := by
    have hne : (fun z : ℂ => P.evalAt f + (z - extChartAt 𝓘(ℂ, ℂ) P P) * g z)
        =ᶠ[nhdsWithin (extChartAt 𝓘(ℂ, ℂ) P P) {extChartAt 𝓘(ℂ, ℂ) P P}ᶜ]
        (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f) := by
      filter_upwards [hgeq, hB5.filter_mono nhdsWithin_le_nhds] with z h2 h3
      have h4 : Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f - P.evalAt f
          = (z - extChartAt 𝓘(ℂ, ℂ) P P) * g z := by
        rw [← h3, h2]
        simp [smul_eq_mul]
      linear_combination -h4
    refine eventuallyEq_nhds_of_eventuallyEq_nhdsNE hne ?_
    simp
  have hnorm : AnalyticAt ℂ
      (fun z : ℂ => P.evalAt f + (z - extChartAt 𝓘(ℂ, ℂ) P P) * g z)
      (extChartAt 𝓘(ℂ, ℂ) P P) :=
    analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul hgan)
  have hstrict : HasStrictDerivAt
      (fun z : ℂ => P.evalAt f + (z - extChartAt 𝓘(ℂ, ℂ) P P) * g z)
      (g (extChartAt 𝓘(ℂ, ℂ) P P)) (extChartAt 𝓘(ℂ, ℂ) P P) := by
    have hid : HasStrictDerivAt (fun z : ℂ => z - extChartAt 𝓘(ℂ, ℂ) P P) (1 - 0)
        (extChartAt 𝓘(ℂ, ℂ) P P) :=
      (hasStrictDerivAt_id _).sub (hasStrictDerivAt_const _ _)
    have hmul := hid.mul hgan.hasStrictDerivAt
    have := hmul.const_add (P.evalAt f)
    simpa using this
  refine ⟨hnorm.congr heq, ?_⟩
  have hd1 : deriv (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f)
      (extChartAt 𝓘(ℂ, ℂ) P P)
      = deriv (fun z : ℂ => P.evalAt f + (z - extChartAt 𝓘(ℂ, ℂ) P P) * g z)
        (extChartAt 𝓘(ℂ, ℂ) P P) :=
    Filter.EventuallyEq.deriv_eq heq.symm
  rw [hd1, hstrict.hasDerivAt.deriv]
  exact hgne

theorem analyticCoord_fields_of_agree {F : Type*} [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [T2Space (Place ℂ F)]
    (hF : ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ))
    (hrat : ∀ P : Place ℂ F, P.IsRational)
    {f : F} (hf : Transcendental ℂ f)
    (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ)
    (hread : ∀ Q ∈ ζ.source, ζ Q = Place.evalAt Q f)
    (P : Place ℂ F) (hP : P ∈ ζ.source)
    (hfP : f ∈ P.toValuationSubring)
    (hord : P.ord (f - algebraMap ℂ F (P.evalAt f)) = 1) :
    AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ∧
    deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ≠ 0 := by
  obtain ⟨han, hder⟩ := analyticAt_read_of_ord_eq_one hF hrat P hf hfP hord
  have hev : (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) P).symm z) f)
      =ᶠ[nhds (extChartAt 𝓘(ℂ, ℂ) P P)] (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) := by
    have hsrc : ∀ᶠ z in nhds (extChartAt 𝓘(ℂ, ℂ) P P),
        (extChartAt 𝓘(ℂ, ℂ) P).symm z ∈ ζ.source := by
      have hcont := continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) P
      have hmem : ζ.source ∈ nhds ((extChartAt 𝓘(ℂ, ℂ) P).symm (extChartAt 𝓘(ℂ, ℂ) P P)) := by
        rw [PartialEquiv.left_inv _ (mem_extChartAt_source (I := 𝓘(ℂ, ℂ)) P)]
        exact ζ.open_source.mem_nhds hP
      exact hcont.eventually_mem hmem
    filter_upwards [hsrc] with z hz
    exact (hread _ hz).symm
  exact ⟨han.congr hev, by rwa [← Filter.EventuallyEq.deriv_eq hev]⟩

end AnalyticCoordAgree

theorem solution {F : Type*} [Field F] [Algebra ℂ F]
    [IsCurveOver ℂ F] [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [T2Space (Place ℂ F)]
    (hF : ∀ g : F, g ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) g)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord g : WithTop ℤ))
    (hrat : ∀ P : Place ℂ F, P.IsRational)
    {f : F} (hf : Transcendental ℂ f)
    (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ)
    (hread : ∀ Q ∈ ζ.source, ζ Q = Place.evalAt Q f)
    (P : Place ℂ F) (hP : P ∈ ζ.source)
    (hfP : f ∈ P.toValuationSubring)
    (hord : P.ord (f - algebraMap ℂ F (P.evalAt f)) = 1) :
    AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ∧
    deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ≠ 0 := by
  exact AnalyticCoordAgree.analyticCoord_fields_of_agree (hF := hF) (hrat := hrat) (hf := hf) (ζ := ζ) (hread := hread) (P := P) (hP := hP) (hfP := hfP) (hord := hord)
