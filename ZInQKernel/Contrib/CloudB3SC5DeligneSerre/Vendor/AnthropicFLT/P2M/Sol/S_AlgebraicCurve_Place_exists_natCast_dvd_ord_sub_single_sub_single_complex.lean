/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_exists_natCast_dvd_ord_sub_single_sub_single_complex (git blob 9a9e7925c6ff3004db18a1583f1aca6d06ad47ce, sha256 a314c44652154ff209f30343a81e93bb2c5f9bdce70caf05e7a0736320d3ce12).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_ComplexLineIntegral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_Place_exists_natCast_dvd_ord_sub_single_sub_single_complex.AlgebraicCurve
end P2MW.S_AlgebraicCurve_Place_exists_natCast_dvd_ord_sub_single_sub_single_complex.AlgebraicCurve

namespace P2MW.S_AlgebraicCurve_Place_exists_natCast_dvd_ord_sub_single_sub_single_complex

set_option autoImplicit false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_Place_exists_natCast_dvd_ord_sub_single_sub_single_complex.AlgebraicCurve
open scoped Manifold ContDiff

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place Divisor Divisor.degree Divisor.degree_single Divisor.IsPrincipal Pic Pic0 IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed HasCanonicalDivisor Place.evalAt regularDifferentials abelJacobiDiv pathPeriodLattice Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice finite_and_finrank_regularDifferentials_eq_genus hasCanonicalDivisor_of_isCurveOver essFiniteType_of_transcendental_of_finiteDimensional)
namespace PlaceDivisibilityComplexAJ
open _root_.AlgebraicCurve

theorem degree_single_sub_single {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] [IsCurveOver K F] (P Q : Place K F) :
    Divisor.degree (Finsupp.single P 1 - Finsupp.single Q 1 : Divisor K F) = 0 := by
  rw [map_sub, Divisor.degree_single, Divisor.degree_single,
    IsCurveOver.deg_eq_one_of_isAlgClosed P, IsCurveOver.deg_eq_one_of_isAlgClosed Q]
  simp

theorem natCast_dvd_of_eq {n : ℕ} {a d e : ℤ} (h : d - (n : ℤ) * e = a) : (n : ℤ) ∣ a - d :=
  ⟨-e, by rw [← h]; ring⟩

theorem exists_sub_nsmul_isPrincipal
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
    {m : ℕ} (b : Module.Basis (Fin m) ℂ ↥(regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (n : ℕ) (hn : n ≠ 0) (D : Divisor ℂ F) (hD0 : Divisor.degree D = 0) :
    ∃ E : Divisor ℂ F, Divisor.IsPrincipal (D - n • E) := by

  set A : Divisor ℂ F →+ (Fin m → ℂ) := abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ with hA
  set Λ : Submodule ℤ (Fin m → ℂ) := pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ])) with hΛ

  set u : Fin m → ℂ := ((n : ℂ)⁻¹) • A D with hu
  have hnu : n • u = A D := by
    rw [hu, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn),
      one_smul]

  obtain ⟨E, hE0, hE⟩ :=
    exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice F hfg hF b P₀ u
  refine ⟨E, ?_⟩

  have hdeg : Divisor.degree (D - n • E) = 0 := by
    rw [map_sub, map_nsmul, hD0, hE0, smul_zero, sub_zero]

  have hmem : A (D - n • E) ∈ Λ := by
    have h1 : n • (A E - u) ∈ Λ := Λ.nsmul_mem hE n
    have h2 : A (D - n • E) = -(n • (A E - u)) := by
      rw [map_sub, map_nsmul, nsmul_sub, hnu]
      abel
    rw [h2]
    exact Λ.neg_mem h1

  exact Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice F hfg hF b P₀ (D - n • E)
    hdeg hmem

theorem exists_natCast_dvd_ord_sub
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] (n : ℕ) (hn : n ≠ 0) (D : Divisor ℂ F) (hD0 : Divisor.degree D = 0) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place ℂ F, (n : ℤ) ∣ v.ord f - D v := by

  obtain ⟨x, hx, hxfd⟩ := hfg
  haveI : Algebra.EssFiniteType ℂ F := essFiniteType_of_transcendental_of_finiteDimensional hx hxfd
  haveI : HasCanonicalDivisor (K := ℂ) (F := F) := hasCanonicalDivisor_of_isCurveOver

  obtain ⟨_instTop, _instCharted, _instManifold, _instCompact, _instT2, _instConn, hF⟩ :=
    Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex F ⟨x, hx, hxfd⟩

  obtain ⟨hfin, -⟩ := finite_and_finrank_regularDifferentials_eq_genus (K := ℂ) (F := F)
  haveI := hfin
  let b := Module.finBasis ℂ ↥(regularDifferentials ℂ F)

  by_cases hP : Nonempty (Place ℂ F)
  · obtain ⟨P₀⟩ := hP
    obtain ⟨E, f, hf, hfE⟩ :=
      exists_sub_nsmul_isPrincipal F ⟨x, hx, hxfd⟩ hF b P₀ n hn D hD0
    refine ⟨f, hf, fun v => natCast_dvd_of_eq (e := E v) ?_⟩
    have := hfE v
    rw [Finsupp.sub_apply, Finsupp.smul_apply, nsmul_eq_mul] at this
    exact this
  · exact ⟨1, one_ne_zero, fun v => (hP ⟨v⟩).elim⟩

end AlgebraicCurve.PlaceDivisibilityComplexAJ

open AlgebraicCurve.PlaceDivisibilityComplexAJ in
theorem solution
    (F : Type*) [Field F] [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧
      FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F]
    (n : ℕ) (hn : n ≠ 0) (P Q : Place ℂ F) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place ℂ F,
      (n : ℤ) ∣ v.ord f - (Finsupp.single P 1 - Finsupp.single Q 1 : Divisor ℂ F) v :=
  exists_natCast_dvd_ord_sub F hfg n hn _ (degree_single_sub_single P Q)
