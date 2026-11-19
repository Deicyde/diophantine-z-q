import ZInQKernel.Contrib.CloudB3RC53.OldKummer.Mattuck
import ZInQKernel.Contrib.CloudB3RC53.Mattuck.NonVacuity
import ZInQKernel.Contrib.OneProof.RC.KummerMaps.NonVacuity

/-!
# Old Kummer, part 4: non-vacuity

Every hypothesis of `natCard_actualKummerAt_one`, `genCondDim2_oldKummer_actual` and
`genCondDim2_oldKummer_actual_odd` is inhabited, over `ℚ`, at the place `v₃` above `3` with
`S = {v₃}`:

* `E = y² = x³ − x` (the Mattuck lane's `W0`), `h = 1` with square root `s = 1` (RC29's
  `one_sq_KS`), `α = alphaOne S 1` (open kernel, locally quadratic everywhere; RC29);
* `FullTorsion ℚ S E 2` (`E = (x − 0)(x − 1)(x + 1)`, RC28's `fullTorsion_two_cubicCurve`);
* the local integral model `C = W0` over `𝒪_{v₃}`, which is a model of the actual local twist
  `E^{(1)} ×_ℚ ℚ₃` (`baseChange_W0_eq_localTwist`), elliptic, with full rational `2`-torsion
  (Mattuck lane's `natCard_twoTorsion_W0`); `2 ∉ v₃`.

`oldKummerActualOdd_nonvacuous`: the conclusion `|H⁰(U_v)| · |H¹(U_v)| = 2⁴` at these data.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.OldKummer

open NumberField IsDedekindDomain WeierstrassCurve ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps ZInQ.Contrib.CloudB3RC53.Mattuck
  ZInQ.Manuscript.RC.TwistDictionary
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

/-- The place of `ℚ` above `3`. -/
def v3 : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := (Ideal.span {(3 : ℤ)}).comap (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ)
  isPrime := by
    have : (Ideal.span {(3 : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_three
    exact Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    have hmem : Rat.ringOfIntegersEquiv.symm 3 ∈
        (Ideal.span {(3 : ℤ)}).comap (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) := by
      rw [Ideal.mem_comap]
      change Rat.ringOfIntegersEquiv (Rat.ringOfIntegersEquiv.symm 3) ∈ _
      rw [RingEquiv.apply_symm_apply]
      exact Ideal.subset_span rfl
    rw [h, Ideal.mem_bot] at hmem
    have h3 := congrArg Rat.ringOfIntegersEquiv hmem
    rw [RingEquiv.apply_symm_apply, map_zero] at h3
    norm_num at h3

theorem two_not_mem_v3 : (2 : 𝓞 ℚ) ∉ v3.asIdeal := by
  intro h
  change (2 : 𝓞 ℚ) ∈ (Ideal.span {(3 : ℤ)}).comap (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) at h
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at h
  change (3 : ℤ) ∣ Rat.ringOfIntegersEquiv 2 at h
  rw [map_ofNat] at h
  norm_num at h

/-- `S = {v₃}`. -/
abbrev S3 : Set (HeightOneSpectrum (𝓞 ℚ)) := {v3}

/-- `v₃ ∈ S`. -/
abbrev pv3 : Places ℚ S3 := ⟨v3, rfl⟩

instance isElliptic_W0_rat : (W0 ℚ).IsElliptic := isElliptic_W0 ℚ

theorem W0_eq_cubicCurve : W0 ℚ = cubicCurve 0 1 (-1) := by
  ext <;> simp [W0, cubicCurve]

/-- `FullTorsion ℚ S (y² = x³ − x) 2`. PROVED. -/
theorem fullTorsion_W0 (S : Set (HeightOneSpectrum (𝓞 ℚ))) : FullTorsion ℚ S (W0 ℚ) (2 ^ 1) := by
  rw [pow_one, W0_eq_cubicCurve]
  exact fullTorsion_two_cubicCurve (by norm_num) (by norm_num) (by norm_num)

/-- **The integral model `W0` over `𝒪_v` is a model of the actual local twist** `E^{(1)} ×_ℚ ℚ_v`
for `E = W0` (the twist by `1` of `y² = x³ − x` is itself). PROVED. -/
theorem baseChange_W0_eq_localTwist (v : HeightOneSpectrum (𝓞 ℚ)) :
    (W0 (v.adicCompletionIntegers ℚ)).baseChange (v.adicCompletion ℚ) = localTwist (W0 ℚ) 1 v := by
  rw [baseChange_W0]
  ext <;> simp [localTwist, twistK, W0, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.baseChange, WeierstrassCurve.map]

theorem isElliptic_baseChange_W0 (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((W0 (v.adicCompletionIntegers ℚ)).baseChange (v.adicCompletion ℚ)).IsElliptic := by
  have := charZero_adicCompletion ℚ v
  rw [baseChange_W0]; exact isElliptic_W0 _

open scoped Classical in
theorem natCard_twoTorsion_baseChange_W0 (v : HeightOneSpectrum (𝓞 ℚ)) :
    Nat.card (Submodule.torsionBy ℤ
      ((W0 (v.adicCompletionIntegers ℚ)).baseChange (v.adicCompletion ℚ)).toAffine.Point 2) = 4 := by
  have := charZero_adicCompletion ℚ v
  rw [baseChange_W0]; exact natCard_twoTorsion_W0 _

open scoped Classical in
/-- **Non-vacuity of `genCondDim2_oldKummer_actual_odd`** (and of the hypotheses of
`natCard_actualKummerAt_one`, `genCondDim2_oldKummer_actual`): over `ℚ` at `v₃`, for
`y² = x³ − x`, `h = s = 1`, `α = alphaOne`, the actual Kummer condition at `i = 1` has
`|H⁰| · |H¹| = 2^(LocalCondition.dim .oldKummer 0)`. PROVED. -/
theorem oldKummerActualOdd_nonvacuous :
    Nat.card ((actualKummerAt (W0 ℚ) 1 1 (one_sq_KS S3) one_ne_zero (alphaOne S3 1)
        (fullTorsion_W0 S3) pv3 (isLocallyQuadAt_alphaOne S3 1 v3)).U.toCC.homology 0) *
      Nat.card ((actualKummerAt (W0 ℚ) 1 1 (one_sq_KS S3) one_ne_zero (alphaOne S3 1)
        (fullTorsion_W0 S3) pv3 (isLocallyQuadAt_alphaOne S3 1 v3)).U.toCC.homology 1) =
      2 ^ ZInQ.Manuscript.RC.Limits.LocalCondition.dim .oldKummer 0 :=
  have := isElliptic_baseChange_W0 v3
  genCondDim2_oldKummer_actual_odd (W0 ℚ) 1 (one_sq_KS S3) one_ne_zero (alphaOne S3 1)
    (fullTorsion_W0 S3) pv3 (isLocallyQuadAt_alphaOne S3 1 v3) two_not_mem_v3
    (W0 (v3.adicCompletionIntegers ℚ)) (baseChange_W0_eq_localTwist v3)
    (natCard_twoTorsion_baseChange_W0 v3)

end ZInQ.Contrib.CloudB3RC53.OldKummer
