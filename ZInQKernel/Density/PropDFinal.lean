import ZInQKernel.Density.PropD
import ZInQKernel.DensitySieve

/-!
# Proposition D, unconditionally (pd-paper §6.1 file 9)

pd-sieve's `uniformBadBound` (`ZInQKernel/Density/GaussSieve.lean`) proves the body of
`UniformBadBound` (Proposition 4.2 via the Selberg sieve). Together with
`goodPrimeDensity_of_uniformBadBound` this gives `ZInQ.GoodPrimeDensity` as a theorem, and hence
`ZInQ.GoodPrimeAP` from Green–Tao's dense theorem alone.
-/

namespace ZInQ.Density

/-- **Proposition 4.2.** The uniform bad-prime bound holds (pd-sieve). -/
theorem uniformBadBound_holds : UniformBadBound := by
  obtain ⟨A, N₁, hA, h⟩ := uniformBadBound
  refine ⟨A, N₁, hA, fun N hN ℓ hℓ h4 h5 hN4 => ?_⟩
  convert h N hN ℓ hℓ h4 h5 hN4 using 4
  exact Iff.rfl

/-- **Proposition D (weak form).** The good slope primes have positive relative upper density in
the primes. -/
theorem goodPrimeDensity : GoodPrimeDensity :=
  goodPrimeDensity_of_uniformBadBound uniformBadBound_holds

/-- **Hypothesis 22P_AP from Green–Tao's dense theorem alone.** -/
theorem goodPrimeAP_of_greenTaoDense' (hGT : GreenTaoDense) : GoodPrimeAP :=
  goodPrimeAP_of_greenTaoDense hGT goodPrimeDensity

end ZInQ.Density
