import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LstarBridge

/-!
# GenusOdd: the final-`k` bridge without `omegaMinus Lat ≠ 0`

`gzComparison_of_scaled` needs `omegaMinus Lat ≠ 0`. For the genuine period lattice this is true
(the lattice of `E/ℚ` is stable under complex conjugation), but its proof needs the uniqueness of
the lattice with given `g₂, g₃` (Laurent recursion for the Eisenstein sums), which is not in Mathlib.
It is not needed if the Manin–Drinfeld input is taken in its natural form "`L_*(h_*)` is a
NONZERO rational" (tex L2403: "a negative genus partner `h_*` with `L_*(h_*) ≠ 0`"):
`gzComparison_of_scaledMD` (PROVED).
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST

/-- **`RCSteps.gz_comparison` for a scaled `L_*`, Manin–Drinfeld form** (PROVED): as
`gzComparison_of_scaled`, with `omegaMinus Lat ≠ 0` replaced by `L_*(h_*) ∈ ℚ^×`. -/
theorem gzComparison_of_scaledMD (P : Prints) (G : GlueAfterRC19) {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]
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
  exact gzComparison_of_scaled P G hf hLat hNC hκ hgp ⟨q, hq⟩ hk0 hk4 hksq hk2N hkcop S selG selR
    hselG hselR (omegaMinus_ne_zero_of hLs) hL'

end ZInQ.Contrib.CloudB3RC53.GenusOdd
