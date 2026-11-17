/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed (git blob f6570ee65a985746f014ad551de8dbe53c1fa62b, sha256 0b39420cb0f83825bba3bbacd875f03b394117f1f2a4374d412b4f49df446e78).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_zero_of_genusReached
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_of_isAlgClosed_of_finite
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_sum_support
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed

set_option autoImplicit false
set_option maxHeartbeats 4000000

open AlgebraicCurve

namespace W7XChildE

theorem constantsAreBase {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ConstantsAreBase K F := by
  obtain ⟨x, hxt, _⟩ := hfg
  haveI : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  refine le_antisymm (fun f hf => ?_) (fun f ⟨c, hc⟩ => hc ▸ fun v =>
    Place.adicValuation_algebraMap_le_one v c)
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  have hord : ∀ v : Place K F, 0 ≤ v.ord f := fun v => by
    have := (mem_riemannRochSpace_iff.mp hf v).resolve_left hf0; simpa using this
  obtain ⟨Df, hDord, hDdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) f hf0
  have hdiv : ∀ v : Place K F, v.ord f = 0 := by
    by_contra hne; push_neg at hne; obtain ⟨v, hv⟩ := hne
    refine absurd hDdeg (ne_of_gt ?_)
    rw [Divisor.degree_eq_sum_support]
    refine Finset.sum_pos' (fun w _ => mul_nonneg (by rw [hDord w]; exact hord w)
      (Int.natCast_nonneg _)) ⟨v, ?_, ?_⟩
    · simp only [Finsupp.mem_support_iff, hDord v]; exact hv
    · rw [hDord v]
      haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
      have : (v.deg : ℤ) = 1 := by exact_mod_cast Place.deg_eq_one_of_isAlgClosed_of_finite v
      rw [this, mul_one]; exact (hord v).lt_of_ne' hv
  exact ⟨_, (Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed x hxt
    (F := F) hdiv).choose_spec⟩

end W7XChildE

open W7XChildE

theorem solution
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K']
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    [IsCurveOver K F] [IsCurveOver K' F']
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (lift : Place K F → Place K' F')
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (hlift_inj : Function.Injective lift) :
    ∃ D : Divisor K F, indexOfSpecialty (K := K') (Finsupp.mapDomain lift D) = 0 := by
  classical

  obtain ⟨x, hxt, hxfd⟩ := id hfg
  obtain ⟨x', hxt', hxfd'⟩ := id hfg'
  haveI : Algebra.EssFiniteType K F :=
    essFiniteType_of_transcendental_of_finiteDimensional hxt hxfd
  haveI : Algebra.EssFiniteType K' F' :=
    essFiniteType_of_transcendental_of_finiteDimensional hxt' hxfd'
  have hCAB : ConstantsAreBase K F := constantsAreBase hfg
  have hCAB' : ConstantsAreBase K' F' := constantsAreBase hfg'

  obtain ⟨hne, hfd0, γ, D₀, hD₀⟩ := stichtenothGenusExists_of_isCurveOver (K := K) (F := F) hCAB
  obtain ⟨hne', hfd0', γ', D₀', hD₀'⟩ :=
    stichtenothGenusExists_of_isCurveOver (K := K') (F := F') hCAB'
  haveI := hne; haveI := hfd0; haveI := hne'; haveI := hfd0'

  obtain ⟨P₀⟩ := hne

  obtain ⟨n, hRGA⟩ :=
    exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists hD₀' (lift P₀)

  refine ⟨Finsupp.single P₀ (n : ℤ), ?_⟩
  have hmap : (Finsupp.mapDomain lift (Finsupp.single P₀ (n : ℤ)) : Divisor K' F')
      = (n : ℤ) • Finsupp.single (lift P₀) (1 : ℤ) := by
    rw [Finsupp.mapDomain_single, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hmap]
  exact indexOfSpecialty_eq_zero_of_genusReached hRGA
