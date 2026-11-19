import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.HeightDischarge
import ZInQKernel.Contrib.OneProof.RC.Even.EvenSource

/-!
# GenusOdd: (3.4) for any period normalization of `L_*` (bridge to
`Even.CentralNormalization.Lstar`)

(3.4) only involves `L_*` at negative arguments (`hk' < 0`, `h_* < 0`) and only through the
difference `v₂ L_*(hk') − v₂ L_*(h_*)`, so it does not depend on the choice of the imaginary period
(tex L2439 "up to the one fixed initial period convention"; tex L7177). This file makes that
precise:

* `LstarScaled E L'`: `L' : ℤ → ℚ` is a normalized central value for some nonzero period `Ω'`:
  `L'(d) = √|d| L(E^{(d)}, 1) / Ω'` for every `d < 0`.
* `lstarScaled_of_centralNormalization`: `Even.CentralNormalization.Lstar` is one
  (period `|Ω⁻|`), given entire continuations of the negative twists (PROVED).
* `gzEveryCompanion_of_scaled`, `gzComparison_of_scaled`: (3.4) at every rough companion and at the
  final `k` (the forms of `gzEveryCompanion_of_RC19`, `gzComparison_of_RC19`) for any such `L'` in
  place of `LstarQ`, with the same `C_per = 0` (PROVED): `L'(d) = λ · L_*(d)` for `d < 0` with
  `λ = Ω_Lat / Ω'`, and `λ` is rational because `L'(h_*)` and `L_*(h_*)` are nonzero rationals.
-/

noncomputable section

open NumberField

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST

/-- `L'` is a normalized central value at negative arguments for some nonzero period `Ω'`. -/
def LstarScaled (E : WeierstrassCurve ℚ) (L' : ℤ → ℚ) : Prop :=
  ∃ Ω' : ℝ, Ω' ≠ 0 ∧ ∀ d : ℤ, d < 0 →
    ((L' d : ℚ) : ℂ) = ((Real.sqrt |(d : ℝ)| : ℝ) : ℂ) * Lval (qtwist E d) / ((Ω' : ℝ) : ℂ)

/-- **`Even.CentralNormalization.Lstar` is a scaled `L_*`** (PROVED), given entire continuations of
the twists by negative integers (modularity with Hecke's theory, GLUE in the RC tree). -/
theorem lstarScaled_of_centralNormalization {E : WeierstrassCurve ℚ}
    (N : ZInQ.Manuscript.RC.Even.CentralNormalization E)
    (hcont : ∀ d : ℤ, d < 0 → ∃ F, IsLContinuation (qtwist E d) F) : LstarScaled E N.Lstar := by
  refine ⟨N.Ωm, N.Ωm_pos.ne', fun d hd => ?_⟩
  obtain ⟨F, hF⟩ := hcont d hd
  have := N.anchor d hd.ne F hF
  rw [if_neg (by omega)] at this
  rw [Lval_eq hF]
  have hc : (((N.Lstar d : ℚ) : ℝ) : ℂ) = ((N.Lstar d : ℚ) : ℂ) := by push_cast; rfl
  rw [← hc, this]

/-- Transport of the valuation difference from `LstarQ` to a scaled `L'` (PROVED). -/
theorem padicValRat_diff_of_scaled {E : WeierstrassCurve ℚ} {Lat : PeriodPair} {L' : ℤ → ℚ}
    (hL' : LstarScaled E L') {a b : ℤ} (ha : a < 0) (hb : b < 0)
    (hLa : Lstar E Lat a ≠ 0) (hLb : Lstar E Lat b ≠ 0)
    (hqb : ∃ q : ℚ, (q : ℂ) = Lstar E Lat b) :
    padicValRat 2 (L' a) - padicValRat 2 (L' b) =
      padicValRat 2 (LstarQ E Lat a) - padicValRat 2 (LstarQ E Lat b) ∧
    (L' a ≠ 0 → LstarQ E Lat a ≠ 0) := by
  obtain ⟨Ω', hΩ', hrel⟩ := hL'
  have hΩ : ((omegaMinus Lat : ℝ) : ℂ) ≠ 0 := by
    intro h0; apply hLa; unfold Lstar; rw [h0, div_zero]
  have hΩ'c : ((Ω' : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hΩ'
  -- `L'(d) = μ · L_*(d)` with `μ = Ω_Lat / Ω'`
  set μ : ℂ := ((omegaMinus Lat : ℝ) : ℂ) / ((Ω' : ℝ) : ℂ) with hμ
  have hμ0 : μ ≠ 0 := div_ne_zero hΩ hΩ'c
  have hscale : ∀ d : ℤ, d < 0 → ((L' d : ℚ) : ℂ) = μ * Lstar E Lat d := fun d hd => by
    rw [hrel d hd, hμ]; unfold Lstar; field_simp
  obtain ⟨qb, hqb⟩ := hqb
  have hqb0 : qb ≠ 0 := by rintro rfl; apply hLb; rw [← hqb]; simp
  -- `μ` is rational
  set lam : ℚ := L' b / qb
  have hmulam : μ = (lam : ℂ) := by
    have := hscale b hb
    rw [← hqb] at this
    have hqbc : (qb : ℂ) ≠ 0 := by exact_mod_cast hqb0
    simp only [lam]; push_cast
    rw [this]; field_simp
  have hlam0 : lam ≠ 0 := by
    intro h0; apply hμ0; rw [hmulam, h0]; simp
  have hLa' : ((L' a / lam : ℚ) : ℂ) = Lstar E Lat a := by
    have := hscale a ha
    rw [hmulam] at this
    have hlamc : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam0
    push_cast; rw [this]; field_simp
  have hLb' : ((L' b / lam : ℚ) : ℂ) = Lstar E Lat b := by
    have := hscale b hb
    rw [hmulam] at this
    have hlamc : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam0
    push_cast; rw [this]; field_simp
  rw [LstarQ_eq hLa', LstarQ_eq hLb']
  have hL'a : L' a ≠ 0 := by
    intro h0; apply hLa; rw [← hLa', h0]; simp
  have hL'b : L' b ≠ 0 := by
    intro h0; apply hLb; rw [← hLb', h0]; simp
  refine ⟨?_, fun _ => div_ne_zero hL'a hlam0⟩
  rw [padicValRat.div hL'a hlam0, padicValRat.div hL'b hlam0]
  ring

theorem Lstar_ne_zero_of {E : WeierstrassCurve ℚ} {Lat : PeriodPair} {b : ℤ}
    (hΩ : omegaMinus Lat ≠ 0) (hb : b ≠ 0) (hLv : Lval (qtwist E b) ≠ 0) :
    Lstar E Lat b ≠ 0 := by
  unfold Lstar
  have hsq : ((Real.sqrt |(b : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt |(b : ℝ)| := Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast hb))
    exact_mod_cast this.ne'
  exact div_ne_zero (mul_ne_zero hsq hLv) (by exact_mod_cast hΩ)

theorem omegaMinus_ne_zero_of {E : WeierstrassCurve ℚ} {Lat : PeriodPair} {a : ℤ}
    (h : Lstar E Lat a ≠ 0) : omegaMinus Lat ≠ 0 := by
  intro h0; apply h; unfold Lstar; rw [h0]; simp

theorem Lval_ne_zero_of_analyticRank_zero {E : WeierstrassCurve ℚ} (h : AnalyticRank E 0) :
    Lval E ≠ 0 := by
  obtain ⟨F, hF, hF1⟩ := analyticRank_zero_iff.mp h
  rw [Lval_eq hF]; exact hF1

/-- **(3.4) at every rough companion for a scaled `L_*`** (PROVED from `Prints` and
`GlueAfterRC19`): `gzEveryCompanion_of_RC19` with `LstarQ` replaced by any `L'` satisfying
`LstarScaled`, e.g. `Even.CentralNormalization.Lstar`; `C_per = 0`. -/
theorem gzEveryCompanion_of_scaled (P : Prints) (G : GlueAfterRC19) {E : WeierstrassCurve ℚ}
    [E.IsElliptic] (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf E Lat) (hNC : IsNonCMLattice Lat) {κ : ℂ}
    (hκ : IsParamScale (newformLevel E) f Lat κ) {hstar : ℤ} (hgp : GenusPartner E hstar)
    (hElkikMD : ∃ q : ℚ, (q : ℂ) = Lstar E Lat hstar)
    (selG : (h : ℤ) → Option (HeegnerDatum E f Lat κ (h * hstar) 1 hstar))
    (selR : (h k : ℤ) → Option (HeegnerDatum E f Lat κ k h.natAbs h))
    (hselG : ∀ h, Prepared E hstar h → AnalyticRank (qtwist E h) 1 → (selG h).isSome)
    (hselR : ∀ h k', Prepared E hstar h → AnalyticRank (qtwist E h) 1 →
      Companion E Lat hstar h k' → (selR h k').isSome)
    {L' : ℤ → ℚ} (hL' : LstarScaled E L') :
    GzEveryCompanion (Prepared E hstar) (fun h => AnalyticRank (qtwist E h) 1) L'
      (jgenOf E f Lat κ hstar selG) (jrcOf E f Lat κ selR) hstar (Companion E Lat hstar) 0 := by
  intro h k' hp hz hk
  obtain ⟨ε, hε, heq⟩ := gzEveryCompanion_of_RC19 P G h₁ h₃ hf hLat hNC hκ hgp hElkikMD selG
    selR hselG hselR h k' hp hz hk
  refine ⟨ε, hε, ?_⟩
  have hLa : Lstar E Lat (h * k') ≠ 0 := hk.2.2.2.2.2
  have hb0 : hstar ≠ 0 := hgp.1.ne
  have hLb : Lstar E Lat hstar ≠ 0 :=
    Lstar_ne_zero_of (omegaMinus_ne_zero_of hLa) hb0
      (Lval_ne_zero_of_analyticRank_zero hgp.2.2.2.2.2)
  have ha : h * k' < 0 := mul_neg_of_pos_of_neg hp.1 hk.1
  rw [heq, (padicValRat_diff_of_scaled hL' ha hgp.1 hLa hLb hElkikMD).1]

/-- **`RCSteps.gz_comparison` for a scaled `L_*`** (PROVED from `Prints` and `GlueAfterRC19`):
`gzComparison_of_RC19` with `LstarQ` replaced by any `L'` satisfying `LstarScaled`; the extra input
`omegaMinus Lat ≠ 0` (the period lattice of `E` has a nonzero imaginary period) replaces the
genuine `L_*(hk) ≠ 0` of the companion relation. -/
theorem gzComparison_of_scaled (P : Prints) (G : GlueAfterRC19) {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat) (hNC : IsNonCMLattice Lat) {κ : ℂ}
    (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ) {hstar kfin : ℤ}
    (hgp : GenusPartner (Ecurve ℓ) hstar)
    (hElkikMD : ∃ q : ℚ, (q : ℂ) = Lstar (Ecurve ℓ) Lat hstar)
    (hk0 : kfin < 0) (hk4 : kfin % 4 = 1) (hksq : Squarefree kfin)
    (hk2N : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → SquareAt p kfin)
    (hkcop : IsCoprime kfin hstar) (S : Finset ℕ)
    (selG : (h : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ (h * hstar) 1 hstar))
    (selR : (h k : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ k h.natAbs h))
    (hselG : ∀ h, Prepared (Ecurve ℓ) hstar h → AnalyticRank (qtwist (Ecurve ℓ) h) 1 →
      (selG h).isSome)
    (hselR : ∀ h, Prepared (Ecurve ℓ) hstar h → AnalyticRank (qtwist (Ecurve ℓ) h) 1 →
      Companion (Ecurve ℓ) Lat hstar h kfin → (selR h kfin).isSome)
    (hΩ : omegaMinus Lat ≠ 0) {L' : ℤ → ℚ} (hL' : LstarScaled (Ecurve ℓ) L') :
    GzComparisonText ℓ (Prepared (Ecurve ℓ) hstar) L'
      (jgenOf (Ecurve ℓ) f Lat κ hstar selG) (jrcOf (Ecurve ℓ) f Lat κ selR) hstar kfin S := by
  obtain ⟨Cper, H⟩ := gzComparison_of_RC19 P G hf hLat hNC hκ hgp hElkikMD hk0 hk4 hksq hk2N
    hkcop S selG selR hselG hselR
  refine ⟨Cper, fun h hp hz hL hq => ?_⟩
  have ha : h * kfin < 0 := mul_neg_of_pos_of_neg hp.1 hk0
  -- `L(E^{(hk)}, 1) ≠ 0` from `L'(hk) ≠ 0`
  have hLv : Lval (qtwist (Ecurve ℓ) (h * kfin : ℤ)) ≠ 0 := by
    obtain ⟨Ω', -, hrel⟩ := hL'
    intro h0
    apply hL
    have := hrel _ ha
    rw [h0, mul_zero, zero_div] at this
    exact_mod_cast this
  have hLa : Lstar (Ecurve ℓ) Lat (h * kfin) ≠ 0 :=
    Lstar_ne_zero_of hΩ ha.ne hLv
  have hLb : Lstar (Ecurve ℓ) Lat hstar ≠ 0 :=
    Lstar_ne_zero_of hΩ hgp.1.ne
      (Lval_ne_zero_of_analyticRank_zero hgp.2.2.2.2.2)
  obtain ⟨hdiff, hne⟩ := padicValRat_diff_of_scaled hL' ha hgp.1 hLa hLb hElkikMD
  obtain ⟨ε, hε, heq⟩ := H h hp hz (hne hL) hq
  exact ⟨ε, hε, by rw [heq, hdiff]⟩

end ZInQ.Contrib.CloudB3RC53.GenusOdd
