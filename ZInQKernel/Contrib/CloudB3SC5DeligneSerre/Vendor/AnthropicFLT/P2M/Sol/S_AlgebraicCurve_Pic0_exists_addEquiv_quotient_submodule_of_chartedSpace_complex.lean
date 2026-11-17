/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_of_chartedSpace_complex (git blob 0e202f70fdc28a9568e5ec4505120489131c81ed, sha256 072ff5f046e96465e0e6c2b9ff994ddfb3546f306271c782fdd0a262c303f013).
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
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_discreteTopology_pathPeriodLattice_and_span_eq_top
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_of_chartedSpace_complex.AlgebraicCurve
end P2MW.S_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_of_chartedSpace_complex.AlgebraicCurve

namespace P2MW.S_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_of_chartedSpace_complex

set_option autoImplicit false

noncomputable section

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_Pic0_exists_addEquiv_quotient_submodule_of_chartedSpace_complex.AlgebraicCurve
open scoped Manifold ContDiff

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place Divisor Divisor.degree Divisor.degZero Divisor.mem_degZero Divisor.IsPrincipal Divisor.mem_principal Pic Pic0 Pic0.mk Pic0.mk_surjective IsCurveOver HasCanonicalDivisor genus Place.evalAt regularDifferentials abelJacobiDiv pathPeriodLattice discreteTopology_pathPeriodLattice_and_span_eq_top abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice finite_and_finrank_regularDifferentials_eq_genus essFiniteType_of_transcendental_of_finiteDimensional)
namespace Pic0ComplexTorusProof
open _root_.AlgebraicCurve

theorem free_finite_finrank_of_discrete_of_span_eq_top {n : ℕ} (L : Submodule ℤ (Fin n → ℂ))
    [DiscreteTopology L] (hspan : Submodule.span ℝ (L : Set (Fin n → ℂ)) = ⊤) :
    Module.Free ℤ L ∧ Module.Finite ℤ L ∧ Module.finrank ℤ L = 2 * n := by
  haveI : IsZLattice ℝ L := ⟨hspan⟩
  haveI hfin : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  haveI hfree : Module.Free ℤ L := ZLattice.module_free ℝ L
  refine ⟨hfree, hfin, ?_⟩
  rw [ZLattice.rank ℝ L, finrank_real_of_complex, Module.finrank_fin_fun]

section AbelJacobi

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

def ajDegZero {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F) :
    Divisor.degZero (K := ℂ) (F := F) →+ (Fin n → ℂ) ⧸ pathPeriodLattice b :=
  ((pathPeriodLattice b).mkQ.toAddMonoidHom.comp (abelJacobiDiv b P₀)).comp
    (Divisor.degZero (K := ℂ) (F := F)).subtype

theorem ajDegZero_apply {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F)
    (D : Divisor.degZero (K := ℂ) (F := F)) :
    ajDegZero b P₀ D = (pathPeriodLattice b).mkQ (abelJacobiDiv b P₀ (D : Divisor ℂ F)) := rfl

theorem ajDegZero_eq_zero_iff {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F)
    (D : Divisor.degZero (K := ℂ) (F := F)) :
    ajDegZero b P₀ D = 0 ↔ abelJacobiDiv b P₀ (D : Divisor ℂ F) ∈ pathPeriodLattice b := by
  rw [ajDegZero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

def ajPic0 {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F)
    (habel : ∀ D : Divisor ℂ F, Divisor.IsPrincipal D →
      abelJacobiDiv b P₀ D ∈ pathPeriodLattice b) :
    Pic0 ℂ F →+ (Fin n → ℂ) ⧸ pathPeriodLattice b :=
  QuotientAddGroup.lift _ (ajDegZero b P₀) fun D hD => by
    rw [AddSubgroup.mem_addSubgroupOf, Divisor.mem_principal] at hD
    exact (ajDegZero_eq_zero_iff b P₀ D).2 (habel _ hD)

theorem ajPic0_mk {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F)
    (habel : ∀ D : Divisor ℂ F, Divisor.IsPrincipal D →
      abelJacobiDiv b P₀ D ∈ pathPeriodLattice b)
    (D : Divisor.degZero (K := ℂ) (F := F)) :
    ajPic0 b P₀ habel (Pic0.mk D) = ajDegZero b P₀ D := rfl

theorem ajPic0_injective {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F)
    (habel : ∀ D : Divisor ℂ F, Divisor.IsPrincipal D →
      abelJacobiDiv b P₀ D ∈ pathPeriodLattice b)
    (hconv : ∀ D : Divisor ℂ F, Divisor.degree D = 0 →
      abelJacobiDiv b P₀ D ∈ pathPeriodLattice b → Divisor.IsPrincipal D) :
    Function.Injective (ajPic0 b P₀ habel) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective q
  rw [ajPic0_mk, ajDegZero_eq_zero_iff] at hq
  have hD0 : Divisor.degree (D : Divisor ℂ F) = 0 := Divisor.mem_degZero.1 D.2
  change (QuotientAddGroup.mk D : Pic0 ℂ F) = 0
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, Divisor.mem_principal]
  exact hconv _ hD0 hq

theorem ajPic0_surjective {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F)
    (habel : ∀ D : Divisor ℂ F, Divisor.IsPrincipal D →
      abelJacobiDiv b P₀ D ∈ pathPeriodLattice b)
    (hjac : ∀ u : Fin n → ℂ, ∃ D : Divisor ℂ F, Divisor.degree D = 0 ∧
      abelJacobiDiv b P₀ D - u ∈ pathPeriodLattice b) :
    Function.Surjective (ajPic0 b P₀ habel) := by
  intro q
  obtain ⟨u, rfl⟩ := (pathPeriodLattice b).mkQ_surjective q
  obtain ⟨D, hD0, hDu⟩ := hjac u
  refine ⟨Pic0.mk ⟨D, Divisor.mem_degZero.2 hD0⟩, ?_⟩
  rw [ajPic0_mk, ajDegZero_apply, Submodule.mkQ_apply, Submodule.mkQ_apply]
  exact (Submodule.Quotient.eq _).2 hDu

end AbelJacobi

end AlgebraicCurve.Pic0ComplexTorusProof

open AlgebraicCurve.Pic0ComplexTorusProof in

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
          (extChartAt 𝓘(ℂ, ℂ) v v) = (v.ord f : WithTop ℤ)) :
    ∃ (L : Submodule ℤ (Fin (genus ℂ F) → ℂ)),
      Module.Free ℤ L ∧ Module.Finite ℤ L ∧
      Module.finrank ℤ L = 2 * genus ℂ F ∧
      Nonempty (Pic0 ℂ F ≃+ (Fin (genus ℂ F) → ℂ) ⧸ L) := by
  classical

  obtain ⟨x, hx, hfd⟩ := id hfg
  haveI : Algebra.EssFiniteType ℂ F :=
    essFiniteType_of_transcendental_of_finiteDimensional hx hfd
  obtain ⟨hfinΩ, hrk⟩ := finite_and_finrank_regularDifferentials_eq_genus (K := ℂ) (F := F)
  haveI := hfinΩ
  let b : Module.Basis (Fin (genus ℂ F)) ℂ ↥(regularDifferentials ℂ F) :=
    Module.finBasisOfFinrankEq ℂ _ hrk

  obtain ⟨P₀⟩ : Nonempty (Place ℂ F) := inferInstance

  obtain ⟨hdisc, hspan⟩ := discreteTopology_pathPeriodLattice_and_span_eq_top F hfg hF b
  haveI := hdisc
  obtain ⟨hfree, hfin, hrank⟩ :=
    free_finite_finrank_of_discrete_of_span_eq_top (pathPeriodLattice fun i => (b i : Ω[F⁄ℂ])) hspan

  have habel : ∀ D : Divisor ℂ F, Divisor.IsPrincipal D →
      abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ D ∈ pathPeriodLattice fun i => (b i : Ω[F⁄ℂ]) :=
    fun D hD => abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal F hfg hF (fun i => b i) P₀ D hD
  have hconv : ∀ D : Divisor ℂ F, Divisor.degree D = 0 →
      abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ D ∈ pathPeriodLattice (fun i => (b i : Ω[F⁄ℂ])) →
        Divisor.IsPrincipal D :=
    fun D hD0 hD => Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice F hfg hF b P₀ D hD0 hD
  have hjac : ∀ u : Fin (genus ℂ F) → ℂ, ∃ D : Divisor ℂ F, Divisor.degree D = 0 ∧
      abelJacobiDiv (fun i => (b i : Ω[F⁄ℂ])) P₀ D - u ∈ pathPeriodLattice fun i => (b i : Ω[F⁄ℂ]) :=
    fun u => exists_degree_eq_zero_and_abelJacobiDiv_sub_mem_pathPeriodLattice F hfg hF b P₀ u

  exact ⟨pathPeriodLattice fun i => (b i : Ω[F⁄ℂ]), hfree, hfin, hrank,
    ⟨AddEquiv.ofBijective (ajPic0 (fun i => (b i : Ω[F⁄ℂ])) P₀ habel)
      ⟨ajPic0_injective _ P₀ habel hconv, ajPic0_surjective _ P₀ habel hjac⟩⟩⟩
