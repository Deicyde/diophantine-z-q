import DirectLevelOneArithmeticV004
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.CoefficientConjugation
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.KnownFieldCoefficientCoordinates

/-!
# Derived coefficient conjugation on actual level-one forms

The rational spanning theorem supplies a finite family for each input.
All-row field-coordinate descent and finite scalar conjugation then
construct a unique genuine modular form with the conjugated coefficients.
No automorphism is applied pointwise to a holomorphic function.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups ModularForm BigOperators

namespace DirectLevelOneGaloisModel

open DirectLevelOneArithmetic

/-- A finite actual rational family representing this particular form. -/
def FiniteRationalRepresentation {k : ℤ} (f : ModularForm 𝒮ℒ k) : Prop :=
  ∃ J : Type, ∃ hJ : Fintype J,
    letI := hJ
    ∃ F : J → ModularForm 𝒮ℒ k, ∃ c : J → ℂ,
      (∀ j, IsRat (F j)) ∧ f = ∑ j, c j • F j

/-- The finite family is produced from the proved span, not supplied as an arithmetic basis. -/
theorem finite_rational_representation {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    FiniteRationalRepresentation f := by
  classical
  have hf : f ∈ Submodule.span ℂ {g : ModularForm 𝒮ℒ k | IsRat g} := by
    change f ∈ rationalSpan k
    rw [rationalSpan_all]
    exact Submodule.mem_top
  refine Submodule.span_induction (p := fun g _ => FiniteRationalRepresentation g)
    ?_ ?_ ?_ ?_ hf
  · intro g hg
    refine ⟨Unit, inferInstance, (fun _ => g), (fun _ => 1), (fun _ => hg), ?_⟩
    simp
  · refine ⟨Empty, inferInstance, Empty.elim, Empty.elim, (fun j => Empty.elim j), ?_⟩
    simp
  · intro f g _ _ hf hg
    obtain ⟨J, hJ, F, c, hF, hf⟩ := hf
    obtain ⟨K, hK, G, d, hG, hg⟩ := hg
    letI := hJ
    letI := hK
    refine ⟨Sum J K, inferInstance, Sum.elim F G, Sum.elim c d, ?_, ?_⟩
    · intro j
      cases j with
      | inl j => exact hF j
      | inr j => exact hG j
    · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hf, hg]
  · intro a f _ hf
    obtain ⟨J, hJ, F, c, hF, hf⟩ := hf
    letI := hJ
    refine ⟨J, hJ, F, (fun j => a * c j), hF, ?_⟩
    rw [hf, Finset.smul_sum]
    simp only [smul_smul]

/-- The genuine level-one coefficient model for any intermediate field over the rationals. -/
theorem exists_unique_coefficient_conjugate (k : ℤ) (K : IntermediateField ℚ ℂ)
    (σ : K ≃ₐ[ℚ] K) (f : ModularForm 𝒮ℒ k)
    (hf : ∀ n : ℕ, (qExpansion 1 f).coeff n ∈ K) :
    ∃! fσ : ModularForm 𝒮ℒ k,
      ∀ n : ℕ, (qExpansion 1 fσ).coeff n =
        (σ (⟨(qExpansion 1 f).coeff n, hf n⟩ : K) : ℂ) := by
  classical
  obtain ⟨J, hJ, F, c, hF, hrep⟩ := finite_rational_representation f
  letI := hJ
  have hFK : ∀ j n, (qExpansion 1 (F j)).coeff n ∈ K := by
    intro j n
    obtain ⟨q, hq⟩ := hF j n
    rw [hq]
    exact KnownFieldCoefficientCoordinates.rational_mem K q
  have hconj : ∀ j n, (qExpansion 1 (F j)).coeff n =
      (σ (⟨(qExpansion 1 (F j)).coeff n, hFK j n⟩ : K) : ℂ) := by
    intro j n
    obtain ⟨q, hq⟩ := hF j n
    have hqmap := (Rat.castHom ℂ).map_rat_algebraMap q
    change (q : ℂ) = algebraMap ℚ ℂ q at hqmap
    have hqA := hq.trans hqmap
    have hsub : (⟨(qExpansion 1 (F j)).coeff n, hFK j n⟩ : K) = algebraMap ℚ K q := by
      apply Subtype.ext
      simpa only [IntermediateField.coe_algebraMap_apply] using hqA
    rw [hsub, σ.commutes]
    simpa only [IntermediateField.coe_algebraMap_apply] using hqA
  exact ModularFormCoefficientConjugation.exists_unique_conjugate
    one_pos one_mem_strictPeriods_SL K F F hFK σ hconj f hf c hrep

end DirectLevelOneGaloisModel
