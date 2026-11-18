import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Artin34
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LstarBridgeMD

/-!
# GenusOdd: the downstream forms of (3.4) with `ArtinFactorization` the only GLUE (PROVED)

`gzEveryCompanion_of_artin` (AppGEndpoints' `FinalFamilyField` input), `gzComparison_of_artin`
(`RCSteps.gz_comparison`), and their scaled-`L_*` versions (lane RC11's normalization):
the same statements as `gzEveryCompanion_genuine`, `gzComparison_genuine`,
`gzEveryCompanion_of_scaled`, `gzComparison_of_scaled`, from `Prints` and `ArtinFactorization`.
-/

noncomputable section

open NumberField

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST

/-- **(3.4) at every `(h, k')` at the genuine objects** (PROVED from `Prints`, `Glue34`): for any
selections of genus and ring-class data defined wherever `h` is a prepared simple zero and `k'` a
companion, with `C_per = 0`. -/
theorem gzEveryCompanion_of_artin (P : Prints) (hArtin : ArtinFactorization) {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf E Lat) (hNC : IsNonCMLattice Lat) {κ : ℂ}
    (hκ : IsParamScale (newformLevel E) f Lat κ) {hstar : ℤ} (hgp : GenusPartner E hstar)
    (hElkikMD : ∃ q : ℚ, (q : ℂ) = Lstar E Lat hstar)
    (selG : (h : ℤ) → Option (HeegnerDatum E f Lat κ (h * hstar) 1 hstar))
    (selR : (h k : ℤ) → Option (HeegnerDatum E f Lat κ k h.natAbs h))
    (hselG : ∀ h, Prepared E hstar h → AnalyticRank (qtwist E h) 1 → (selG h).isSome)
    (hselR : ∀ h k', Prepared E hstar h → AnalyticRank (qtwist E h) 1 →
      Companion E Lat hstar h k' → (selR h k').isSome) :
    GzEveryCompanion (Prepared E hstar) (fun h => AnalyticRank (qtwist E h) 1) (LstarQ E Lat)
      (jgenOf E f Lat κ hstar selG) (jrcOf E f Lat κ selR) hstar (Companion E Lat hstar) 0 := by
  intro h k' hp hz hk
  obtain ⟨datG, hdG⟩ := Option.isSome_iff_exists.mp (hselG h hp hz)
  obtain ⟨datR, hdR⟩ := Option.isSome_iff_exists.mp (hselR h k' hp hz hk)
  obtain ⟨-, -, ε, hε, heq⟩ := core34' P hArtin h₁ h₃ hf hLat hNC hκ hgp hElkikMD hp hz hk datG datR
  refine ⟨ε, hε, ?_⟩
  simp only [jgenOf, jrcOf, hdG, hdR]
  rw [heq]
  ring

/-- **`RCSteps.gz_comparison` at the genuine objects** (PROVED from `Prints`, `Glue34`) for the
curve `E_ℓ`, at a final companion `k` that is a negative odd fundamental discriminant, a unit square
at every prime of `2N`, prime to `h_*` (tex L2604–2613 with L2349–2352), when `D.prepared` is the
genuine `Prepared` and `D.Lstar, D.jgen, D.jrc` are `LstarQ, jgenOf, jrcOf` (with `C_per = 0`). -/
theorem gzComparison_of_artin (P : Prints) (hArtin : ArtinFactorization) {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]
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
      Companion (Ecurve ℓ) Lat hstar h kfin → (selR h kfin).isSome) :
    GzComparisonText ℓ (Prepared (Ecurve ℓ) hstar) (LstarQ (Ecurve ℓ) Lat)
      (jgenOf (Ecurve ℓ) f Lat κ hstar selG) (jrcOf (Ecurve ℓ) f Lat κ selR) hstar kfin S := by
  refine ⟨0, fun h hp hz hL hq => ?_⟩
  have h₁ : (Ecurve ℓ).a₁ = 0 := rfl
  have h₃ : (Ecurve ℓ).a₃ = 0 := rfl
  have hodd : h % 2 = 1 := by
    have := (hp.2.2.1 2 Nat.prime_two (dvd_mul_right 2 _)).2.1 rfl
    omega
  have hk : Companion (Ecurve ℓ) Lat hstar h kfin := by
    refine ⟨hk0, hk4, hksq, fun p hp' hpd => ?_, hkcop, ?_⟩
    · have hp'' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp'
      rcases hp''.dvd_or_dvd hpd with h1 | h1
      · exact hk2N p hp' (by exact_mod_cast h1)
      · have hp2 : p ≠ 2 := by
          rintro rfl
          obtain ⟨m, hm⟩ := h1
          omega
        exact squareAt_of_jacobiSym hp' hp2 (hq p hp' h1).2
    · rw [← LstarQ_spec hL]
      exact_mod_cast hL
  obtain ⟨datG, hdG⟩ := Option.isSome_iff_exists.mp (hselG h hp hz)
  obtain ⟨datR, hdR⟩ := Option.isSome_iff_exists.mp (hselR h hp hz hk)
  obtain ⟨-, -, ε, hε, heq⟩ := core34' P hArtin h₁ h₃ hf hLat hNC hκ hgp hElkikMD hp hz hk datG datR
  refine ⟨ε, hε, ?_⟩
  simp only [jgenOf, jrcOf, hdG, hdR]
  rw [heq]
  ring

/-- **(3.4) at every rough companion for a scaled `L_*`** (PROVED from `Prints` and
`GlueAfterRC19`): `gzEveryCompanion_of_RC19` with `LstarQ` replaced by any `L'` satisfying
`LstarScaled`, e.g. lane RC11's normalization; `C_per = 0`. -/
theorem gzEveryCompanion_of_scaled_artin (P : Prints) (hArtin : ArtinFactorization) {E : WeierstrassCurve ℚ}
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
  obtain ⟨ε, hε, heq⟩ := gzEveryCompanion_of_artin P hArtin h₁ h₃ hf hLat hNC hκ hgp hElkikMD selG
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
theorem gzComparison_of_scaled_artin (P : Prints) (hArtin : ArtinFactorization) {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]
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
  obtain ⟨Cper, H⟩ := gzComparison_of_artin P hArtin hf hLat hNC hκ hgp hElkikMD hk0 hk4 hksq hk2N
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

/-- **`RCSteps.gz_comparison` for a scaled `L_*`, Manin–Drinfeld form** (PROVED): as
`gzComparison_of_scaled`, with `omegaMinus Lat ≠ 0` replaced by `L_*(h_*) ∈ ℚ^×`. -/
theorem gzComparison_of_scaledMD_artin (P : Prints) (hArtin : ArtinFactorization) {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat) (hNC : IsNonCMLattice Lat) {κ : ℂ}
    (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ) {hstar kfin : ℤ}
    (hgp : GenusPartner (Ecurve ℓ) hstar)
    (hElkikMD : ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = Lstar (Ecurve ℓ) Lat hstar)
    (hk0 : kfin < 0) (hk4 : kfin % 4 = 1) (hksq : Squarefree kfin)
    (hk2N : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → SquareAt p kfin)
    (hkcop : IsCoprime kfin hstar) (S : Finset ℕ)
    (selG : (h : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ (h * hstar) 1 hstar))
    (selR : (h k : ℤ) → Option (HeegnerDatum (Ecurve ℓ) f Lat κ k h.natAbs h))
    (hselG : ∀ h, Prepared (Ecurve ℓ) hstar h → AnalyticRank (qtwist (Ecurve ℓ) h) 1 →
      (selG h).isSome)
    (hselR : ∀ h, Prepared (Ecurve ℓ) hstar h → AnalyticRank (qtwist (Ecurve ℓ) h) 1 →
      Companion (Ecurve ℓ) Lat hstar h kfin → (selR h kfin).isSome)
    {L' : ℤ → ℚ} (hL' : LstarScaled (Ecurve ℓ) L') :
    GzComparisonText ℓ (Prepared (Ecurve ℓ) hstar) L'
      (jgenOf (Ecurve ℓ) f Lat κ hstar selG) (jrcOf (Ecurve ℓ) f Lat κ selR) hstar kfin S := by
  obtain ⟨q, hq0, hq⟩ := hElkikMD
  have hLs : Lstar (Ecurve ℓ) Lat hstar ≠ 0 := by
    rw [← hq]; exact_mod_cast hq0
  exact gzComparison_of_scaled_artin P hArtin hf hLat hNC hκ hgp ⟨q, hq⟩ hk0 hk4 hksq hk2N hkcop S selG selR
    hselG hselR (omegaMinus_ne_zero_of hLs) hL'

end ZInQ.Contrib.CloudB3RC53.GenusOdd
