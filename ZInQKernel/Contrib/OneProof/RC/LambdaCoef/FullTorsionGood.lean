import ZInQKernel.Contrib.OneProof.RC.LambdaCoef.Tate
import ZInQKernel.Contrib.RC53Assist.DivisionPoints.Support

/-!
# Theorem 5.3: full 2-power torsion from good reduction

Lane RC28 keeps `HasFullTwoTorsion K S W` (`E[2^∞] ⊆ E(K_S)`) as a GLUE input, citing the criterion
of Néron, Ogg and Shafarevich (Silverman AEC VII.7.1). The implication actually used, from good
reduction outside `S` to full torsion over `K_S`, is now proved in the tree
(`DivisionPoints.fullTorsion_of_goodReduction`). This file records the consequence for the class:
when `S` contains the places above `2` and `W` has good reduction outside `S`, the class holds.
-/

namespace ZInQ.Manuscript.RC.LambdaCoef

open NumberField IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  {W : WeierstrassCurve K} [W.IsElliptic]

/-- **Full 2-power torsion from good reduction** (PROVED): if `S` contains the places above `2`
and `W` has good reduction at every place outside `S`, then `E(K_S)[2^n]` has `4^n` points for
every `n`. -/
theorem hasFullTwoTorsion_of_goodReduction
    (h2 : ∀ v : HeightOneSpectrum (𝓞 K), (2 : 𝓞 K) ∈ v.asIdeal → v ∈ S)
    (hgood : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ZInQ.Manuscript.RC.DivisionPoints.HasGoodReductionAt W v) :
    HasFullTwoTorsion K S W where
  full n := by
    classical
    exact ZInQ.Manuscript.RC.DivisionPoints.fullTorsion_of_goodReduction W
      (pow_ne_zero n two_ne_zero)
      (fun v hv => h2 v (v.isPrime.mem_of_pow_mem n (by simpa [Nat.cast_pow] using hv))) hgood

end ZInQ.Manuscript.RC.LambdaCoef
