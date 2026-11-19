import ZInQKernel.Contrib.OneProof.RC.KummerMaps.KummerImage
import ZInQKernel.Contrib.OneProof.RC.CoefModules.NonVacuity

/-!
# Lane RC29 (Kummer maps), part 5: non-vacuity of the hypotheses of the Kummer maps

Every hypothesis of `Twist.lean`, `LocalGlobal.lean`, `Iota.lean` and `KummerImage.lean` is
inhabited, over `ℚ`, for every set `S` of finite primes and every place `v`:

* the square root `s = 1 ∈ K_S` of `h = 1` (`one_sq_KS`), so `χ_h = quadChar 1`;
* the trivial moving character `ξ = 1`, hence `α = alphaChar i χ_h 1` with open kernel
  (`isOpenKer_alphaOne`) and `IsLocallyQuadAt` at every place (`isLocallyQuadAt_alphaOne`);
* `FullTorsion ℚ S E_1 (2^1)` for `E_1 : y² = x(x − 1)(x + 3)` (lane RC28's
  `fullTorsion_two_curveEll`);
* hence `kummerIota`, `kummerIota_smul`, `actualKummerAt`, `actualKummerAt_range_H1` and
  `kummerSelData` are instantiated (`actualKummerAt_nonvacuous`, `kummerSelData_nonvacuous`).

Kinds: PROVED.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.KummerMaps

open NumberField IsDedekindDomain ZInQ.Manuscript.RC.SelmerComplex ZInQ.Manuscript.RC.CoefModules
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

variable (S : Set (HeightOneSpectrum (𝓞 ℚ)))

/-- PROVED (non-vacuity). `1 ∈ K_S` is a square root of `h = 1`. -/
theorem one_sq_KS : (1 : KS ℚ S) ^ 2 = algebraMap ℚ (KS ℚ S) 1 := by
  rw [one_pow, map_one]

/-- Definition (non-vacuity). The character `α = χ_1 · (1 + t)^0` of `M_i` for `h = 1` and the
trivial moving character. -/
abbrev alphaOne (i : ℕ) : GKS ℚ S →* (Acoef i)ˣ :=
  alphaChar i (quadChar (1 : KS ℚ S) (one_sq_KS S) one_ne_zero)
    (1 : GKS ℚ S →* Multiplicative (ZMod (2 ^ (2 * i))))

/-- PROVED (non-vacuity). `alphaOne` has open kernel. -/
instance isOpenKer_alphaOne (i : ℕ) : IsOpenKer (alphaOne S i) := by
  refine alphaChar_isOpenKer i _ _ ?_
  have : ((1 : GKS ℚ S →* Multiplicative (ZMod (2 ^ (2 * i)))).ker : Set (GKS ℚ S)) =
      Set.univ := by
    ext g
    simp
  rw [this]
  exact isOpen_univ

/-- PROVED (non-vacuity of `IsLocallyQuadAt`). For the trivial moving character the character of
`M_i` is `χ_h` on every decomposition group. -/
theorem isLocallyQuadAt_alphaOne (i : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsLocallyQuadAt i (alphaOne S i) (quadChar (1 : KS ℚ S) (one_sq_KS S) one_ne_zero) v :=
  isLocallyQuadAt_alphaChar i _ 1 v fun _ => rfl

/-- PROVED (non-vacuity of `FullTorsion` at `i = 1`; lane RC28's `fullTorsion_two_curveEll`). -/
theorem fullTorsion_curveEll_one : FullTorsion ℚ S (curveEll (1 : ℚ)) (2 ^ 1) := by
  rw [pow_one]
  exact fullTorsion_two_curveEll one_ne_zero

/-- PROVED (non-vacuity of the hypotheses of `kummerIota`, `kummerIota_smul` and
`actualKummerAt`): the actual Kummer condition exists for `E_1`, `h = 1`, `i = 1` at every place
`v ∈ S`, for every `S`; it is a subcomplex, and its `H¹` image is described by
`actualKummerAt_range_H1`. -/
theorem actualKummerAt_nonvacuous (v : Places ℚ S) :
    ∃ c : CondAt ℚ S (Acoef 1) (Mcoef ℚ S (curveEll (1 : ℚ)) 1 (alphaOne S 1)) v,
      c.IsInjective := by
  have := isElliptic_curveEll (K := ℚ) one_ne_zero
  exact ⟨actualKummerAt (curveEll 1) 1 1 (one_sq_KS S) one_ne_zero (alphaOne S 1)
      (fullTorsion_curveEll_one S) v (isLocallyQuadAt_alphaOne S 1 v.1),
    actualKummerAt_isInjective (curveEll 1) 1 1 (one_sq_KS S) one_ne_zero (alphaOne S 1)
      (fullTorsion_curveEll_one S) v (isLocallyQuadAt_alphaOne S 1 v.1)⟩

/-- PROVED (non-vacuity of the equivariance hypothesis of lane RC28's `kummerAt`): the genuine
`ι_v` for `E_1`, `h = 1`, `i = 1` satisfies it at every place. -/
theorem kummerIota_nonvacuous (v : HeightOneSpectrum (𝓞 ℚ)) :
    haveI := isElliptic_curveEll (K := ℚ) one_ne_zero
    ∀ (σ : Gloc ℚ v) (t : TorsAlg (v.adicCompletion ℚ) (localTwist (curveEll (1 : ℚ)) 1 v) (2 ^ 1)),
      kummerIota (curveEll 1) 1 1 (one_sq_KS S) one_ne_zero (alphaOne S 1)
          (fullTorsion_curveEll_one S) v (σ • t) =
        σ • kummerIota (curveEll 1) 1 1 (one_sq_KS S) one_ne_zero (alphaOne S 1)
          (fullTorsion_curveEll_one S) v t := by
  have := isElliptic_curveEll (K := ℚ) one_ne_zero
  exact kummerIota_smul (curveEll 1) 1 1 (one_sq_KS S) one_ne_zero (alphaOne S 1)
    (fullTorsion_curveEll_one S) v (isLocallyQuadAt_alphaOne S 1 v)

/-- PROVED (non-vacuity of the hypotheses of `kummerSelData` and
`isGaloisSelData_kummerSelData`): with `S₀ = S` finite and Kummer conditions at every place,
the actual Selmer data exist and are genuine Galois Selmer data. -/
theorem kummerSelData_nonvacuous (hSfin : S.Finite) :
    ∃ D : ZInQ.Contrib.CloudB3RC53.PairedFunctional.SelData (Acoef 1),
      ZInQ.Manuscript.RC.Wiring.IsGaloisSelData D := by
  have := isElliptic_curveEll (K := ℚ) one_ne_zero
  exact ⟨_, isGaloisSelData_kummerSelData (subset_refl S) (curveEll 1) 1 1 (one_sq_KS S)
    one_ne_zero (alphaOne S 1) (fullTorsion_curveEll_one S) hSfin S
    (fun v _ => isLocallyQuadAt_alphaOne S 1 v) (fun v _ hP => absurd v.2 hP)
    (fun v _ hP => absurd v.2 hP)⟩

end ZInQ.Manuscript.RC.KummerMaps
