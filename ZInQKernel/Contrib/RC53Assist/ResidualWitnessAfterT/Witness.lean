import ZInQKernel.Contrib.CloudB3RC53.GenuineInst.ResidualAfterTWitness

/-!
# Full-degree residual rank counts at the active witness

The witness of `ResidualWitnessActive/Witness.lean` has number field `ℚ(i)`,
curve `E₁₁`, derivative prime `7`, and active prime `13`. This application of
`residualRankCounts_afterT''` counts every degree in `[0, 3]` and uses the complex
isomorphisms `witness_ered` and `witness_ebc` from `ResidualAfterTWitness.lean`.

The condition term in degree `3` vanishes. The shifted local term in degree `3`
is local `H²` and is included in the local dimension sum. The generic minimal
model is `afterL`, the cohomology of `afterQ'`, reached through the acyclic
comparison blocks after inverting `t`.

The four Milne statements remain explicit hypotheses. This is an application to
the constant extension of the residual cone and the split original-support
model; it does not construct the global power-series character or the arithmetic
cochains with Laurent-series coefficients.
-/

noncomputable section

set_option maxHeartbeats 600000

namespace ZInQ.Contrib.RC53Assist.ResidualWitnessAfterT

open CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain TensorProduct
  ZInQ.Contrib.CloudB3RC53.PairedFunctional
  ZInQ.Contrib.CloudB3RC53.SelmerDuality
  ZInQ.Contrib.CloudB3RC53.GenuineInst
  ZInQ.Contrib.CloudB3RC53.RankCounts
  ZInQ.Contrib.CloudB3RC53.Mattuck
  ZInQ.Manuscript.RC.SelmerComplex
  ZInQ.Manuscript.RC.Limits
  ZInQ.Contrib.RC53Assist.ResidualWitnessActive

open scoped Classical

/-- The global comparison on the entire required interval `[0, 2]`. -/
def actEG_full (n : ℤ) (hn : n ∈ Finset.Icc (0 : ℤ) 2) :
    actSel.G.X n ≃ₗ[ZMod 2]
      genH SmallK (primesAboveSet SmallK (chargedPrimes 66 5 actD)) n.toNat :=
  actEG n hn

/-- Adding degree `3` preserves the exact Kummer-row condition sum. -/
theorem act_hUm_full_eq (h28 : MilneADT_I_2_8) :
    ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (actSel.U.X n) =
      ∑ p ∈ chargedPrimes 66 5 actD,
        condSum SmallK (genCondDimFun2 SmallK SmallS actCond
          (kummerDimOfCurves SmallK smallLocalModels (kd2OfCurves SmallK smallLocalModels))) p := by
  have : Subsingleton (actSel.U.X 3) := actSel_U_off h28 3 (Or.inr (by norm_num))
  rw [show Finset.Icc (0 : ℤ) 3 = insert 3 actDegrees by decide,
    Finset.sum_insert (by decide), Module.finrank_zero_of_subsingleton, zero_add]
  exact act_hUm_eq h28

/-- The four cone degrees include all three local cohomology degrees. -/
private theorem place_L_full_dims (v : Places SmallK SmallS) :
    ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) ((locCC v.1).homology (n - 1)) =
      genLocDim SmallK SmallS v.1 := by
  have hsum (f : ℤ → ℕ) : ∑ n ∈ Finset.Icc (0 : ℤ) 3, f n =
      f 0 + f 1 + f 2 + f 3 := by
    rw [show Finset.Icc (0 : ℤ) 3 = insert 3 actDegrees by decide,
      Finset.sum_insert (by decide), sum_actDegrees]
    ring
  rw [hsum]
  have : Subsingleton ((locCC v.1).homology ((0 : ℤ) - 1)) :=
    natHomology_negative (contCochains (ZMod 2) (Gloc SmallK v.1) (locM v.1))
      ((0 : ℤ) - 1) (by norm_num)
  rw [Module.finrank_zero_of_subsingleton (M := (locCC v.1).homology ((0 : ℤ) - 1))]
  change 0 + Module.finrank (ZMod 2) ((locCC v.1).homology ((0 : ℕ) : ℤ)) +
      Module.finrank (ZMod 2) ((locCC v.1).homology ((1 : ℕ) : ℤ)) +
      Module.finrank (ZMod 2) ((locCC v.1).homology ((2 : ℕ) : ℤ)) = _
  rw [finrank_full, finrank_full, finrank_full, genLocDim]
  simp [Finset.sum_range_succ]

/-- The full shifted local sum equals the genuine local dimension sum, including `H²`. -/
theorem act_hLm_full_eq (h28 : MilneADT_I_2_8) :
    ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) (actSel.L.X (n - 1)) =
      ∑ p ∈ chargedPrimes 66 5 actD, genLocSum SmallK SmallS p := by
  simp only [finrank_actL h28]
  rw [Finset.sum_comm, Finset.sum_congr rfl genLocSum_eq, ← sum_places locDimFun]
  exact Finset.sum_congr rfl fun v _ => (place_L_full_dims v).trans (locDimFun_place v).symm

/-- The integral smaller-support model is supported in `[0, 3]`. -/
theorem afterP_supported (h410 : MilneADT_I_4_10_totallyComplex) (h28 : MilneADT_I_2_8) :
    afterP.IsStrictlyGE 0 ∧ afterP.IsStrictlyLE 3 := by
  have hsub (n : ℤ) (hn : n < 0 ∨ 3 < n) : Subsingleton (afterP.X n) := by
    have : Subsingleton ((selCx actSel).X n) := actP_X_subsingleton h410 h28 n hn
    have : Unique (Rt ⊗[ZMod 2] (selCx actSel).X n) := TensorProduct.uniqueRight
    change Subsingleton (Rt ⊗[ZMod 2] (selCx actSel).X n)
    infer_instance
  constructor
  · rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    have := hsub n (Or.inl hn)
    exact ModuleCat.isZero_of_subsingleton _
  · rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    have := hsub n (Or.inr hn)
    exact ModuleCat.isZero_of_subsingleton _

/-- The repaired after-`t` constructor at the active witness, counting all degrees `[0, 3]`. -/
def activeAfterTCounts_full (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) : ResidualRankCounts := by
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.G.X n) := actSel_G_finite h410 h51
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.U.X n) := actSel_U_finite h28
  letI : ∀ n, Module.Finite (ZMod 2) (actSel.L.X n) := actSel_L_finite h28
  letI : ∀ n, Module.Free Rt (afterP.X n) := afterP_free
  letI : ∀ n, Module.Finite Rt (afterP.X n) := afterP_finite h410 h51 h28
  letI : afterP.IsStrictlyGE 0 := (afterP_supported h410 h28).1
  letI : afterP.IsStrictlyLE 3 := (afterP_supported h410 h28).2
  letI : afterP'.IsStrictlyGE 0 := afterP'_ge h410 h28
  letI : afterP'.IsStrictlyLE 3 := afterP'_le h410 h28
  letI : afterL.IsStrictlyGE 0 := afterL_ge h410 h28
  letI : afterL.IsStrictlyLE 3 := afterL_le h410 h28
  letI : ∀ n, Module.Finite Kt (afterP'.X n) := afterP'_finite h410 h51 h28
  letI : ∀ n, Module.Finite Kt (afterL.X n) := afterL_finite h410 h51 h28
  exact residualRankCounts_afterT'' SmallK smallLocalModels h410 h51 h28 h23
    (-1) smallAlpha smallAlpha_radicand smallK_complex 66 (by decide) 0 (by simp) 5 (by decide)
    actD actD_prime actD_odd actCond actCond_derivative actCond_full_torsion
    smallInfinitePlace smallInfinitePlace_complex SmallS actSel actEG_full (witness_eG3 h410)
    (act_hUm_full_eq h28).le (act_hLm_full_eq h28).le afterP witness_ered
    afterP' afterL witness_ebc afterL_minimal (afterE h410 h28)

/-- The generic rank is the whole-model rank of the generic original-support cohomology. -/
theorem activeAfterTCounts_full_genericRank (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    (activeAfterTCounts_full h410 h51 h28 h23).genericRank =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank Kt (afterQ'.homology n) := rfl

/-- The total rank includes the local `H²` in cone degree `3`. -/
theorem activeAfterTCounts_full_rankTot (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    (activeAfterTCounts_full h410 h51 h28 h23).rankTot =
      ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) ((selCx actSel).X n) := rfl

/-- Non-vacuity and the numerical residual bound for the repaired full-degree application. -/
theorem residualRankCounts_afterT_active_full (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    2 ≤ (activeAfterTCounts_full h410 h51 h28 h23).genericRank ∧
      (activeAfterTCounts_full h410 h51 h28 h23).genericRank ≤
        (activeAfterTCounts_full h410 h51 h28 h23).rankTot ∧
      (activeAfterTCounts_full h410 h51 h28 h23).genericRank ≤ 294 := by
  refine ⟨?_, (activeAfterTCounts_full h410 h51 h28 h23).transfer, ?_⟩
  · rw [activeAfterTCounts_full_genericRank]
    exact (two_le_afterL_zero h410 h51 h28).trans (Finset.single_le_sum
      (f := fun n => Module.finrank Kt (afterQ'.homology n)) (fun _ _ => Nat.zero_le _)
      (show (0 : ℤ) ∈ Finset.Icc (0 : ℤ) 3 by decide))
  · have hb := (activeAfterTCounts_full h410 h51 h28 h23).genericRank_le
    change (activeAfterTCounts_full h410 h51 h28 h23).genericRank ≤
      residualBoundConstant (2 * 66).primeFactors.card 0 actD.card at hb
    rwa [activeBound] at hb

/-- The full-degree after-`t` estimate, stated directly as finite rank sums. -/
theorem afterT_full_rank_estimate (h410 : MilneADT_I_4_10_totallyComplex)
    (h51 : MilneADT_I_5_1_totallyComplex) (h28 : MilneADT_I_2_8)
    (h23 : MilneADT_I_2_3_trivial) :
    2 ≤ ∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank Kt (afterQ'.homology n) ∧
      (∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank Kt (afterQ'.homology n)) ≤
        (∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank (ZMod 2) ((selCx actSel).X n)) ∧
      (∑ n ∈ Finset.Icc (0 : ℤ) 3, Module.finrank Kt (afterQ'.homology n)) ≤ 294 := by
  have h := residualRankCounts_afterT_active_full h410 h51 h28 h23
  rwa [activeAfterTCounts_full_genericRank, activeAfterTCounts_full_rankTot] at h

end ZInQ.Contrib.RC53Assist.ResidualWitnessAfterT
