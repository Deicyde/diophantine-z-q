import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitivePeterssonTranslationStrip
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Actual integrable parabolic-coset unfolding

A principal-group fundamental domain is tiled along the actual width-N
parabolic cosets. The resulting parabolic domain has the already-proved
integrable zero cusp seed. Absolute summability of the integrals and the
interchange of sum and integral are then derived from the tiled measure.
No unfolding, orthogonality, or sum-integrability hypothesis is supplied.
The primitive-row identification of the periodized seed remains separate.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Set UpperHalfPlane Complex Matrix.SpecialLinearGroup
open scoped Topology MatrixGroups ModularForm Pointwise ComplexConjugate

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitivePetersson

/-- The actual principal-group quotient by its width-N unipotent subgroup. -/
abbrev parabolicQuotient (N : ℕ) := (CongruenceSubgroup.Gamma N) ⧸
  (translationGroup N).subgroupOf (CongruenceSubgroup.Gamma N)

/-- The genuine infinite coset tiling, with inverse representatives. -/
def parabolicTiling (N : ℕ) (D : Set ℍ) : Set ℍ :=
  ⋃ q : parabolicQuotient N, (q.out)⁻¹ • D

/-- Each term is the actual cusp seed transported by the chosen group element. -/
def periodizedSeedTerm (N k : ℕ)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (k : ℤ))
    (q : parabolicQuotient N) (τ : ℍ) : ℂ := hyperSeed k f ((q.out)⁻¹ • τ)

lemma parabolicTiling_fundamental (N : ℕ) (D : Set ℍ)
    (hD : IsFundamentalDomain (CongruenceSubgroup.Gamma N) D volume) :
    IsFundamentalDomain (translationGroup N) (parabolicTiling N D) volume := by
  have ht := (hD.subgroup_iUnion_out_inv_smul
    ((translationGroup N).subgroupOf (CongruenceSubgroup.Gamma N))).of_subgroupOf
  rw [inf_of_le_left (translationGroup_le_principal N)] at ht
  exact ht

lemma parabolicTiling_measure (N : ℕ) (D : Set ℍ)
    (hD : IsFundamentalDomain (CongruenceSubgroup.Gamma N) D volume) :
    volume.restrict (parabolicTiling N D) =
      Measure.sum (fun q : parabolicQuotient N => volume.restrict ((q.out)⁻¹ • D)) := by
  apply Measure.restrict_iUnion_ae
  · intro q r hqr
    apply hD.aedisjoint
    intro he
    apply hqr
    rw [← QuotientGroup.out_eq' q,← QuotientGroup.out_eq' r,inv_inj.mp he]
  · intro q
    exact hD.nullMeasurableSet_smul _

/-- Integrability over the infinite parabolic tiling is actually produced. -/
theorem hyperSeed_tiling_integrable_zero (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (k : ℤ))
    (D : Set ℍ) (hD : IsFundamentalDomain (CongruenceSubgroup.Gamma N) D volume) :
    IntegrableOn (hyperSeed k f) (parabolicTiling N D) volume ∧
      (∫ τ in parabolicTiling N D, hyperSeed k f τ) = 0 :=
  hyperSeed_parabolic_domain_zero N k hk f _ (parabolicTiling_fundamental N D hD)

/-- The cusp bound and actual tiling derive summability of all term integrals,
not just pointwise convergence of the original Eisenstein series. -/
theorem periodizedSeed_integrable_summable (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (k : ℤ))
    (D : Set ℍ) (hD : IsFundamentalDomain (CongruenceSubgroup.Gamma N) D volume) :
    (∀ q : parabolicQuotient N, IntegrableOn (periodizedSeedTerm N k f q) D volume) ∧
      Summable (fun q : parabolicQuotient N => ∫ τ in D, ‖periodizedSeedTerm N k f q τ‖) := by
  have hi := (hyperSeed_tiling_integrable_zero N k hk f D hD).1
  rw [IntegrableOn,parabolicTiling_measure N D hD] at hi
  have hc := (integrable_sum_measure_iff).mp hi
  have he (q : parabolicQuotient N) : (∫ τ in (q.out)⁻¹ • D, ‖hyperSeed k f τ‖) =
      ∫ τ in D, ‖periodizedSeedTerm N k f q τ‖ := by
    rw [← Set.image_smul]
    exact (measurePreserving_smul (q.out)⁻¹ volume).setIntegral_image_emb
      (measurableEmbedding_const_smul _) _ _
  refine ⟨?_,?_⟩
  · intro q
    have hq := hc.1 q
    change IntegrableOn (hyperSeed k f) ((q.out)⁻¹ • D) volume at hq
    rw [← Set.image_smul,
      (measurePreserving_smul (q.out)⁻¹ volume).integrableOn_image
        (measurableEmbedding_const_smul _)] at hq
    exact hq
  · simpa only [he] using hc.2

/-- A genuine absolutely convergent coset-unfolding identity, already with
zero right side from the independently proved actual cusp seed integral. -/
theorem periodizedSeed_integral_zero (N : ℕ) [NeZero N] (k : ℕ) (hk : 3 ≤ k)
    (f : CuspForm ((CongruenceSubgroup.Gamma N).map (mapGL ℝ)) (k : ℤ))
    (D : Set ℍ) (hD : IsFundamentalDomain (CongruenceSubgroup.Gamma N) D volume) :
    ∫ τ in D, (∑' q : parabolicQuotient N, periodizedSeedTerm N k f q τ) = 0 := by
  have hc := periodizedSeed_integrable_summable N k hk f D hD
  rw [← integral_tsum_of_summable_integral_norm hc.1 hc.2]
  have hi := hyperSeed_tiling_integrable_zero N k hk f D hD
  have he (q : parabolicQuotient N) : (∫ τ in D, periodizedSeedTerm N k f q τ) =
      ∫ τ in (q.out)⁻¹ • D, hyperSeed k f τ := by
    rw [← Set.image_smul]
    exact ((measurePreserving_smul (q.out)⁻¹ volume).setIntegral_image_emb
      (measurableEmbedding_const_smul _) _ _).symm
  simp only [he]
  rw [IntegrableOn,parabolicTiling_measure N D hD] at hi
  rw [← integral_sum_measure hi.1]
  exact hi.2

end ZInQ.Contrib.HeckePrimeRationality.PrimitivePetersson
