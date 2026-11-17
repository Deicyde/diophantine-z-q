/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Divisor_isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice (git blob d39573e8889268b1aa992d3e6ea12e35eb7160b9, sha256 27e79763e47aa8677cd1f58c181bc58c33513aba9b8195f5ce320247c9525977).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_ordDifferential_ge_neg_one_and_evalAt_eq_of_degree_eq_zero
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_regular_pathIntegral_sub_eq_of_abelJacobiDiv_mem_pathPeriodLattice
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_isPrincipal_of_forall_pathIntegral_eq_two_pi_I_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Divisor_isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice

set_option autoImplicit false

noncomputable section

open AlgebraicCurve
open scoped Manifold ContDiff

namespace AbelSufficiencyGlue

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem (v : Place K F) {g : F} (hg : g ∈ v.toValuationSubring) :
    0 ≤ v.ord g := by
  by_cases hg0 : g = 0
  · simp [hg0]
  by_contra hlt
  push Not at hlt

  have hinv : 0 < v.ord g⁻¹ := by rw [v.ord_inv]; omega
  have hmem : g⁻¹ ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hg0) hinv.le

  have hunit : IsUnit (⟨g, hg⟩ : v.toValuationSubring) :=
    ⟨⟨⟨g, hg⟩, ⟨g⁻¹, hmem⟩, Subtype.ext (mul_inv_cancel₀ hg0),
      Subtype.ext (inv_mul_cancel₀ hg0)⟩, rfl⟩
  have h0 : v.ord g = 0 := by
    have := v.ord_coe_unit hunit.unit
    simpa using this
  omega

theorem dCoordFn_ne_zero (v : Place K F) : v.dCoordFn ≠ 0 := by
  intro h
  have := v.ord_dCoordFn
  rw [h, v.ord_zero] at this
  exact zero_ne_one this

theorem dCoordFn_mem (v : Place K F) : v.dCoordFn ∈ v.toValuationSubring :=
  v.mem_toValuationSubring_of_ord_nonneg_alt (dCoordFn_ne_zero v) (by rw [v.ord_dCoordFn]; norm_num)

theorem dCoordFn_mul_mem_of_le (v : Place K F) {a : F} (ha : -1 ≤ v.ord a) :
    v.dCoordFn * a ∈ v.toValuationSubring := by
  by_cases ha0 : a = 0
  · rw [ha0, mul_zero]; exact zero_mem _
  refine v.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (dCoordFn_ne_zero v) ha0) ?_
  rw [v.ord_mul (dCoordFn_ne_zero v) ha0, v.ord_dCoordFn]
  omega

theorem le_ord_of_dCoordFn_mul_mem (v : Place K F) {a : F}
    (h : v.dCoordFn * a ∈ v.toValuationSubring) : -1 ≤ v.ord a := by
  by_cases ha0 : a = 0
  · rw [ha0, v.ord_zero]; norm_num
  have := ord_nonneg_of_mem v h
  rw [v.ord_mul (dCoordFn_ne_zero v) ha0, v.ord_dCoordFn] at this
  omega

theorem evalAt_add_of_mem (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem evalAt_neg_of_mem (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) : v.evalAt (-f) = -v.evalAt f := by
  apply v.algebraMap_residueField_injective
  rw [map_neg, v.algebraMap_evalAt hv (neg_mem hf), v.algebraMap_evalAt hv hf, ← map_neg]
  rfl

theorem evalAt_dCoordFn (v : Place K F) (hv : v.IsRational) : v.evalAt v.dCoordFn = 0 := by
  apply v.algebraMap_residueField_injective
  rw [v.algebraMap_evalAt hv (dCoordFn_mem v), map_zero, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  have h0 := v.ord_coe_unit hunit.unit
  simp only [IsUnit.unit_spec] at h0
  rw [v.ord_dCoordFn] at h0
  exact one_ne_zero h0

theorem evalAt_dCoordFn_mul_of_mem (v : Place K F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) : v.evalAt (v.dCoordFn * f) = 0 := by
  rw [v.evalAt_mul_of_mem hv (dCoordFn_mem v) hf, evalAt_dCoordFn v hv, zero_mul]

theorem differentialCoeff_sub (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (η ζ : Ω[F⁄K]) :
    v.differentialCoeff (η - ζ) = v.differentialCoeff η - v.differentialCoeff ζ :=
  v.differentialCoeff_unique (by
    rw [sub_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

theorem differentialCoeff_mem_of_mem_regularDifferentials (v : Place K F) [v.DCoordGenerates]
    [Nontrivial Ω[F⁄K]] {ζ : Ω[F⁄K]} (hζ : ζ ∈ regularDifferentials K F) :
    v.differentialCoeff ζ ∈ v.toValuationSubring := by
  obtain ⟨f, hf, hfeq⟩ := (mem_regularDifferentials_iff.1 hζ) v
  rw [v.differentialCoeff_unique hfeq]
  exact hf

theorem isRational_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] (w : Place K F) :
    w.IsRational := by
  haveI : Module.Finite K w.ResidueField := IsCurveOver.finite_residueField w
  haveI : Algebra.IsIntegral K w.ResidueField := Algebra.IsIntegral.of_finite K _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := w.ResidueField)).2

theorem thirdKind_sub [IsAlgClosed K] [IsCurveOver K F] (hgen : ∀ v : Place K F, v.DCoordGenerates)
    (D : Divisor K F) (η ζ : Ω[F⁄K])
    (hη : ∀ v : Place K F, -1 ≤ v.ordDifferential η)
    (hres : ∀ v : Place K F, Place.evalAt v (v.dCoordFn * v.differentialCoeff η) = (D v : K))
    (hζ : ζ ∈ regularDifferentials K F) :
    (∀ v : Place K F, -1 ≤ v.ordDifferential (η - ζ)) ∧
      ∀ v : Place K F, Place.evalAt v (v.dCoordFn * v.differentialCoeff (η - ζ)) = (D v : K) := by
  have key : ∀ v : Place K F,
      v.dCoordFn * v.differentialCoeff (η - ζ) ∈ v.toValuationSubring ∧
        Place.evalAt v (v.dCoordFn * v.differentialCoeff (η - ζ)) = (D v : K) := by
    intro v
    haveI := hgen v
    have hv := isRational_of_isAlgClosed (K := K) (F := F) v
    have hcoef := differentialCoeff_sub v η ζ
    have hf := differentialCoeff_mem_of_mem_regularDifferentials v hζ
    have ha : v.dCoordFn * v.differentialCoeff η ∈ v.toValuationSubring :=
      dCoordFn_mul_mem_of_le v (hη v)
    have hb : v.dCoordFn * v.differentialCoeff ζ ∈ v.toValuationSubring :=
      mul_mem (dCoordFn_mem v) hf
    have hsplit : v.dCoordFn * v.differentialCoeff (η - ζ) =
        v.dCoordFn * v.differentialCoeff η + -(v.dCoordFn * v.differentialCoeff ζ) := by
      rw [hcoef]; ring
    refine ⟨?_, ?_⟩
    · rw [hsplit]; exact add_mem ha (neg_mem hb)
    · rw [hsplit, evalAt_add_of_mem v hv ha (neg_mem hb), evalAt_neg_of_mem v hv hb,
        evalAt_dCoordFn_mul_of_mem v hv hf, hres v, neg_zero, add_zero]
  refine ⟨fun v => ?_, fun v => (key v).2⟩
  exact le_ord_of_dCoordFn_mul_mem v (key v).1

end AbelSufficiencyGlue

open AbelSufficiencyGlue in
theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]
    [IsManifold 𝓘(ℂ, ℂ) ω (Place ℂ F)] [CompactSpace (Place ℂ F)]
    [T2Space (Place ℂ F)] [ConnectedSpace (Place ℂ F)]
    (hF : ∀ f : F, f ≠ 0 → ∀ v : Place ℂ F,
      MeromorphicAt (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) ∧
      meromorphicOrderAt
          (fun z : ℂ => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f)
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ))
    {n : ℕ} (b : Module.Basis (Fin n) ℂ ↥(regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (D : Divisor ℂ F) (hD0 : Divisor.degree D = 0)
    (hD : abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ D ∈ pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ]))) :
    Divisor.IsPrincipal D := by
  obtain ⟨x, hx, hfd⟩ := hfg
  haveI : Algebra.EssFiniteType ℂ F :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfd
  have hgen : ∀ v : Place ℂ F, v.DCoordGenerates := AlgebraicCurve.dCoordGenerates_of_isCurveOver

  obtain ⟨η, hη, hres⟩ :=
    AlgebraicCurve.exists_ordDifferential_ge_neg_one_and_evalAt_eq_of_degree_eq_zero
      (K := ℂ) ⟨x, hx, hfd⟩ D hD0

  obtain ⟨ζ, hζ, hper⟩ :=
    AlgebraicCurve.exists_regular_pathIntegral_sub_eq_of_abelJacobiDiv_mem_pathPeriodLattice
      F ⟨x, hx, hfd⟩ hF b P₀ D hD0 η hη hres hD

  obtain ⟨hθ, hresθ⟩ := thirdKind_sub (K := ℂ) hgen D η ζ hη hres hζ

  exact AlgebraicCurve.Divisor.isPrincipal_of_forall_pathIntegral_eq_two_pi_I_mul
    F ⟨x, hx, hfd⟩ hF D (η - ζ) hθ hresθ hper

end
