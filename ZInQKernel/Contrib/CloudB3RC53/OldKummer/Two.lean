import ZInQKernel.Contrib.CloudB3RC53.OldKummer.Mattuck
import ZInQKernel.Contrib.CloudB3RC53.Mattuck.Two
import ZInQKernel.Contrib.CloudB3RC53.OldKummer.NonVacuity

/-!
# Old Kummer, part 5: places above `2`

Manuscript `diophantine_zq.tex`, tex 4544–4573 (old Kummer row `4 + d_w` at `w ∣ 2`,
`d_w = [K_w : ℚ₂]`), Lemma `ex:arith-local-kummer` (tex 3413–3438), Mattuck at `p = 2`.

`genCondDim2_oldKummer_actual_two`: at a place `v ∣ 2`, for a local integral model `C` of the
actual local twist with full rational `2`-torsion, RC29's actual Kummer condition at `i = 1` has
`|H⁰(U_v)| · |H¹(U_v)| = 2^(LocalCondition.dim .oldKummer d_v) = 2^(4 + d_v)` (the finiteness of
`C(K_v)/2` comes from the Mattuck lane's lattice `latticeU`).

Non-vacuity (`oldKummerActualTwo_nonvacuous`): over `ℚ` at the place `v₂` above `2`, for
`y² = x³ − x` and `h = 1`.

**Classification.** PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.OldKummer

open NumberField IsDedekindDomain WeierstrassCurve ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.CoefModules ZInQ.Manuscript.RC.KummerMaps ZInQ.Contrib.CloudB3RC53.Mattuck
  ZInQ.Contrib.CloudB3RC53.RankCounts
open ZInQ.Manuscript.RC.HeegnerAlgebra (Acoef)

variable {K : Type} [Field K] [NumberField K] {S : Set (HeightOneSpectrum (𝓞 K))}
  (W : WeierstrassCurve K) [W.IsElliptic] (s : KS K S) {h : K}
  (hs : s ^ 2 = algebraMap K (KS K S) h) (hs0 : s ≠ 0) (α : GKS K S →* (Acoef 1)ˣ) [IsOpenKer α]
  (hFull : FullTorsion K S W (2 ^ 1))

open scoped Classical in
/-- **At a place above `2` the actual Kummer condition has the table's dimension `4 + d_v`**
(tex 4551–4556, Mattuck at `p = 2`). PROVED. -/
theorem genCondDim2_oldKummer_actual_two (v : Places K S)
    (hα : IsLocallyQuadAt 1 α (quadChar s hs hs0) v.1) [v.1.asIdeal.LiesOver (vP two).asIdeal]
    (C : WeierstrassCurve (v.1.adicCompletionIntegers K))
    [(C.baseChange (v.1.adicCompletion K)).IsElliptic]
    (hC : C.baseChange (v.1.adicCompletion K) = localTwist W h v.1)
    (h4 : Nat.card
      (Submodule.torsionBy ℤ (C.baseChange (v.1.adicCompletion K)).toAffine.Point 2) = 4) :
    letI := qpAlg K two v.1
    Nat.card ((actualKummerAt W 1 s hs hs0 α hFull v hα).U.toCC.homology 0) *
        Nat.card ((actualKummerAt W 1 s hs hs0 α hFull v hα).U.toCC.homology 1) =
      2 ^ ZInQ.Manuscript.RC.Limits.LocalCondition.dim .oldKummer
        (Module.finrank ℚ_[2] (v.1.adicCompletion K)) := by
  have := finiteIndex_latticeU K v.1 C
  have hcard := card_modN_two_of_lattice (latticeU K v.1 C) (latticeU_noTwoTorsion K v.1 C)
    (card_modN_latticeU K v.1 C)
  have : Finite (ModN (C.baseChange (v.1.adicCompletion K)).toAffine.Point 2) :=
    Nat.finite_of_card_ne_zero (by rw [hcard, h4]; positivity)
  rw [genCondDim2_oldKummer_actual W s hs hs0 α hFull v hα C hC]
  exact congrArg (2 ^ ·) (kummerResidualDim_two K v.1 C h4)

/-! ### Non-vacuity at the place above `2` -/

/-- The place of `ℚ` above `2`. -/
def v2 : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := (Ideal.span {(2 : ℤ)}).comap (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ)
  isPrime := by
    have : (Ideal.span {(2 : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two
    exact Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    have hmem : Rat.ringOfIntegersEquiv.symm 2 ∈
        (Ideal.span {(2 : ℤ)}).comap (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ) := by
      rw [Ideal.mem_comap]
      change Rat.ringOfIntegersEquiv (Rat.ringOfIntegersEquiv.symm 2) ∈ _
      rw [RingEquiv.apply_symm_apply]
      exact Ideal.subset_span rfl
    rw [h, Ideal.mem_bot] at hmem
    have h2 := congrArg Rat.ringOfIntegersEquiv hmem
    rw [RingEquiv.apply_symm_apply, map_zero] at h2
    norm_num at h2

/-- `v₂` lies over `2`. -/
instance liesOver_v2 : v2.asIdeal.LiesOver (vP two).asIdeal := by
  refine ⟨?_⟩
  rw [vP_asIdeal]
  change _ = Ideal.comap (algebraMap ℤ (𝓞 ℚ))
    ((Ideal.span {(2 : ℤ)}).comap (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ))
  rw [Ideal.comap_comap]
  have : (Rat.ringOfIntegersEquiv : 𝓞 ℚ →+* ℤ).comp (algebraMap ℤ (𝓞 ℚ)) = RingHom.id ℤ :=
    RingHom.ext_int _ _
  rw [this, Ideal.comap_id]
  rfl

/-- `S = {v₂}`. -/
abbrev S2 : Set (HeightOneSpectrum (𝓞 ℚ)) := {v2}

/-- `v₂ ∈ S`. -/
abbrev pv2 : Places ℚ S2 := ⟨v2, rfl⟩

open scoped Classical in
/-- **Non-vacuity of `genCondDim2_oldKummer_actual_two`**: over `ℚ` at `v₂`, for `y² = x³ − x`,
`h = s = 1`, `α = alphaOne`, the actual Kummer condition at `i = 1` has
`|H⁰| · |H¹| = 2^(LocalCondition.dim .oldKummer [ℚ₂ : ℚ₂])`. PROVED. -/
theorem oldKummerActualTwo_nonvacuous :
    letI := qpAlg ℚ two v2
    Nat.card ((actualKummerAt (W0 ℚ) 1 1 (one_sq_KS S2) one_ne_zero (alphaOne S2 1)
        (fullTorsion_W0 S2) pv2 (isLocallyQuadAt_alphaOne S2 1 v2)).U.toCC.homology 0) *
      Nat.card ((actualKummerAt (W0 ℚ) 1 1 (one_sq_KS S2) one_ne_zero (alphaOne S2 1)
        (fullTorsion_W0 S2) pv2 (isLocallyQuadAt_alphaOne S2 1 v2)).U.toCC.homology 1) =
      2 ^ ZInQ.Manuscript.RC.Limits.LocalCondition.dim .oldKummer
        (Module.finrank ℚ_[2] (v2.adicCompletion ℚ)) :=
  have := isElliptic_baseChange_W0 v2
  genCondDim2_oldKummer_actual_two (W0 ℚ) 1 (one_sq_KS S2) one_ne_zero (alphaOne S2 1)
    (fullTorsion_W0 S2) pv2 (isLocallyQuadAt_alphaOne S2 1 v2)
    (W0 (v2.adicCompletionIntegers ℚ)) (baseChange_W0_eq_localTwist v2)
    (natCard_twoTorsion_baseChange_W0 v2)

end ZInQ.Contrib.CloudB3RC53.OldKummer
