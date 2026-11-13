/-
Copyright the authors of Vilin97/Autoformalization (green-tao/), Apache License 2.0;
see ThirdParty/GreenTao/LICENSE.

Adapted from `Submission/GreenTao/ReducedResidueCofinalTransference.lean` (lines 55–157) and
`Submission/GreenTao/FinalTransferenceAssembly.lean` (lines 56–184) at commit
0dc67d87416c19690dd641a178ada32cca95c651.
Modified 2026 for the diophantine-z-q project: the density `δ > 0` is a parameter instead of the
fixed `densityTarget`; the conclusion holds for every large prime modulus (instead of one prime
modulus beyond each bound) and for every weight `f` with `0 ≤ f ≤ wTrickedPrimeWeight` (instead of
the prime weight itself), so that it applies to subsets of the primes.
-/
import Submission

/-!
# Transference for every large prime modulus and every sub-weight

The proof of `hasCofinalPrimeStandardReducedResidueWTrickedPrimeProgressionCounts_of_orderedRemoval_of_linearForms`
with two quantifiers changed. Nothing in it uses that the weight is the prime weight: the relative
counting theorem `relativeAPCount_lower_bound_of_linearFormsCondition` holds for every `f` with
`0 ≤ f ≤ ν`, and every weight below the W-tricked prime weight lies below the majorant `ν`.
-/

namespace ZInQ.GreenTaoDense

open Submission.GreenTao Filter

/-- The transference output, for every density `δ > 0`, every large prime modulus `M + 1`, every
reduced residue `b` modulo `W = primorial w`, and every weight `0 ≤ f ≤ wTrickedPrimeWeight`. -/
def HasPrimeModulusSubweightCounts : Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ δ : ℝ, 0 < δ →
    ∃ (w : ℕ) (c : ℝ), 0 < c ∧
      ∀ᶠ M : ℕ in atTop, Nat.Prime (M + 1) →
        ∀ b ∈ reducedResidues (primorial w), ∀ f : ZMod (M + 1) → ℝ,
          (∀ x, 0 ≤ f x) →
          (∀ x, f x ≤ wTrickedPrimeWeight (primeScale k standardSmoothSieveCutoff.normalizer)
            (primorial w) b x) →
          δ ≤ mean f → c ≤ cyclicAPCount k (M + 1) f

theorem hasPrimeModulusSubweightCounts_of_orderedRemoval_of_linearForms
    (hremoval : HasOrderedRemovalForAllAPLengths)
    (hsieve : HasStandardCyclicMajorantLinearForms) :
    HasPrimeModulusSubweightCounts := by
  intro k hk δ hδ
  obtain ⟨r, rfl⟩ : ∃ r, k = r + 2 := ⟨k - 2, by omega⟩
  have hdenseThreshold : 0 < δ / 2 := by linarith
  obtain ⟨denseCount, hdenseCount, hweighted⟩ :=
    exists_uniformWeightedAPCount_of_orderedRemoval_of_two_le
      (r + 2) (by omega) (hremoval (r + 2) hk) hdenseThreshold
  have hcountReserve : 0 < denseCount / 2 := by linarith
  obtain ⟨P⟩ := RelativeCountingTransferenceParameters.nonempty r hdenseThreshold hcountReserve
  obtain ⟨w, _hwExceptional, hlinearForms⟩ :=
    hsieve (r + 2) hk P.linearFormsError P.linearFormsError_pos
  set W := primorial w with hW
  let ν : (M : ℕ) → ℕ → ZMod (M + 1) → ℝ := fun M b =>
    standardSmoothSieveCutoff.cyclicMajorant (sieveLevel (r + 2) (M + 1)) W b
  have hν_nonneg : ∀ M b (x : ZMod (M + 1)), 0 ≤ ν M b x := fun M b x =>
    standardSmoothSieveCutoff.cyclicMajorant_nonneg
      (one_le_sieveLevel hk (Nat.succ_pos M)) W b x
  have hmajor := eventually_all_residues_wTrickedPrimeWeight_le_cyclicMajorant
    standardSmoothSieveCutoff hk (primorial_pos w)
  have hdensityThreshold :
      δ / 2 + polynomialDenseModelError P.polynomial P.cutError P.approximationError ≤ δ := by
    have := P.denseModelError_lt
    linarith
  refine ⟨w, denseCount - denseCount / 2, by linarith, ?_⟩
  filter_upwards [hmajor, hlinearForms, eventually_gt_atTop (r + 1)] with M hmajorM hLFM hMr
  intro hprime b hb f hf0 hfle hmean
  have hcoprime : Nat.Coprime (M + 1) (Nat.factorial (r + 1)) :=
    hprime.coprime_factorial_of_lt (by omega)
  have hbW : b < W := (mem_reducedResidues.mp hb).1
  exact relativeAPCount_lower_bound_of_linearFormsCondition
    P.approximationError_pos.le P.cutError_pos.le hf0
    (fun x => (hfle x).trans (hmajorM b hbW x))
    (hν_nonneg M b) P.approximates (hLFM b hb) hcoprime P.denseModel_conversion
    (hweighted (M + 1)) (hdensityThreshold.trans hmean)
    (P.relativeAPComparisonLe (hLFM b hb) (hν_nonneg M b) hcoprime)

/-- The transference for every large prime modulus and every sub-weight, from the two deep inputs
of the vendored proof (as in `Submission.green_tao`). -/
theorem hasPrimeModulusSubweightCounts : HasPrimeModulusSubweightCounts :=
  hasPrimeModulusSubweightCounts_of_orderedRemoval_of_linearForms
    (fun k hk => by
      have hrank : k - 1 = (k - 2) + 1 := by omega
      rw [hrank]
      exact hasUniformOrderedPatternRemoval_sourceFull k (k - 2) (by omega))
    hasStandardCyclicMajorantLinearForms

end ZInQ.GreenTaoDense
