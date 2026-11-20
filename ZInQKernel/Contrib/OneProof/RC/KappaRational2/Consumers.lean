import ZInQKernel.Contrib.OneProof.RC.KappaRational2.Periods
import ZInQKernel.Contrib.OneProof.RC.ParamJoin.Assembly
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.FixedScaleElkik

/-! Supply the scale witness before calling any at-scale consumer. -/

noncomputable section

open UpperHalfPlane HeckeRing.GL2
open AlgebraicGeometry CategoryTheory MonObj PkgI3 WeierstrassCurve
open ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.RC.PreparedParam ZInQ.Manuscript.SelmerTwoPower
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd
open scoped Classical MatrixGroups

namespace ZInQ.Manuscript.RC.KappaRational2

/-- Prepared values at the original scale, given an independent reference scale. -/
theorem prepared_values_of_reference_scale {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W}
    {L : ℕ} (s : StageKummer.Setup I L)
    (href : ∃ r : ℚ, IsParamScale (newformLevel (Ecurve ℓ)) I.f I.Lat (r : ℂ))
    (hCM : letI : NeZero (newformLevel (Ecurve ℓ)) := ⟨(StageKummer.positiveLevel s).ne'⟩
           CMFieldOfDefinition (X0Branch.model (newformLevel (Ecurve ℓ)))) :
    ∀ h (hp : Prepared (Ecurve ℓ) W.hstar h),
      StageSelector.PreparedParamValue (Ecurve ℓ) I.f I.Lat I.κ
        (StageKummer.positiveLevel s) I.hgp hp := by
  let _ : NeZero (newformLevel (Ecurve ℓ)) := ⟨(StageKummer.positiveLevel s).ne'⟩
  exact ParamJoin.prepared_values s
    (rational_of_matching_coeffs (Ecurve ℓ) I.f I.hf I.hNC I.hκ href) hCM

/-- Missing stage values at the original scale. -/
theorem missing_values_of_reference_scale {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W}
    {L : ℕ} (s : StageKummer.Setup I L)
    (href : ∃ r : ℚ, IsParamScale (newformLevel (Ecurve ℓ)) I.f I.Lat (r : ℂ))
    (hCM : letI : NeZero (newformLevel (Ecurve ℓ)) := ⟨(StageKummer.positiveLevel s).ne'⟩
           CMFieldOfDefinition (X0Branch.model (newformLevel (Ecurve ℓ)))) :
    StageKummer.MissingParamValues s := by
  let _ : NeZero (newformLevel (Ecurve ℓ)) := ⟨(StageKummer.positiveLevel s).ne'⟩
  exact ParamJoin.missing_values s
    (rational_of_matching_coeffs (Ecurve ℓ) I.f I.hf I.hNC I.hκ href) hCM

/-- Ring class values for the rough companions at the original scale. -/
theorem ring_values_of_reference_scale {ℓ : ℕ} (P : Prints) (hℓ : 0 < ℓ)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2} {Lat : PeriodPair} {κ : ℂ}
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    (hLat : IsLatticeOf (Ecurve ℓ) Lat) (hNC : IsNonCMLattice Lat)
    (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ)
    (href : ∃ r : ℚ, IsParamScale (newformLevel (Ecurve ℓ)) f Lat (r : ℂ))
    (hCM : letI : NeZero (newformLevel (Ecurve ℓ)) := ⟨(Gz34Instance.curve_form P hℓ).1.ne'⟩
           CMFieldOfDefinition (X0Branch.model (newformLevel (Ecurve ℓ)))) {s : ℤ} :
    ∀ h k (hp : Prepared (Ecurve ℓ) s h) (hk : Companion (Ecurve ℓ) Lat s h k),
      Gz34Instance.RingParamValue (Ecurve ℓ) f Lat κ (Gz34Instance.curve_form P hℓ).1 hp hk := by
  let _ : NeZero (newformLevel (Ecurve ℓ)) := ⟨(Gz34Instance.curve_form P hℓ).1.ne'⟩
  exact ParamJoin.ring_values P hℓ hf hLat hκ
    (rational_of_matching_coeffs (Ecurve ℓ) f hf hNC hκ href) hCM

/-- The conductor-one values for the rough companions at the original scale. -/
theorem genus_values_of_reference_scale {ℓ : ℕ} {W : WData ℓ} (P : Prints) (hℓ : 0 < ℓ)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat) (hNC : IsNonCMLattice Lat)
    {κ : ℂ} (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ)
    (href : ∃ r : ℚ, IsParamScale (newformLevel (Ecurve ℓ)) f Lat (r : ℂ))
    (hCM : letI : NeZero (newformLevel (Ecurve ℓ)) := ⟨(Gz34Instance.curve_form P hℓ).1.ne'⟩
           CMFieldOfDefinition (X0Branch.model (newformLevel (Ecurve ℓ))))
    (hpartner : IsGenusPartner ℓ W.hstar)
    (hlevel0 : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ S0 ℓ) :
    ∀ h (hp : Prepared (Ecurve ℓ) W.hstar h),
      StageSelector.PreparedParamValue (Ecurve ℓ) f Lat κ (Gz34Instance.curve_form P hℓ).1
        (Gz34Instance.genusPartner_of_support hpartner hlevel0) hp := by
  let _ : NeZero (newformLevel (Ecurve ℓ)) := ⟨(Gz34Instance.curve_form P hℓ).1.ne'⟩
  exact ParamJoin.genus_values P hℓ hf hLat hκ
    (rational_of_matching_coeffs (Ecurve ℓ) f hf hNC hκ href) hCM hpartner hlevel0

/-- The Elkik and Manin–Drinfeld reduction at the original scale. -/
theorem hElkikMD_of_reference_scale {ℓ : ℕ} [(Ecurve ℓ).IsElliptic] {d : ℤ}
    [NeZero (newformLevel (Ecurve ℓ))]
    (hElkik : ElkikPrint.ManinDrinfeldTorsion (newformLevel (Ecurve ℓ))
      (J0Cusps.algebraicCuspClass (newformLevel (Ecurve ℓ))))
    {f : Newform (newformLevel (Ecurve ℓ)) 2} (hf : PrintsAnalytic.IsNewformOf (Ecurve ℓ) f)
    (hgp : GenusPartner (Ecurve ℓ) d) {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat)
    (hNC : IsNonCMLattice Lat)
    {κ : ℂ} (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f.toCuspForm Lat κ)
    (href : ∃ r : ℚ, IsParamScale (newformLevel (Ecurve ℓ)) f.toCuspForm Lat (r : ℂ)) :
    ∃ q : ℚ, q ≠ 0 ∧ (q : ℂ) = Lstar (Ecurve ℓ) Lat d := by
  let g := f.toCuspFormGamma0 hf.1
  have hg : (g : ℍ → ℂ) = (f.toCuspForm : ℍ → ℂ) := f.coe_toCuspFormGamma0 hf.1
  have hcoef (n : ℕ) (hn : 0 < n) :
      (qExpansion 1 g).coeff n = ((Ecurve ℓ).LFunction n : ℂ) := by
    rw [hg]
    exact hf.2 n hn
  have hκg : IsParamScale (newformLevel (Ecurve ℓ)) g Lat κ := hg.symm ▸ hκ
  have hrefg : ∃ r : ℚ, IsParamScale (newformLevel (Ecurve ℓ)) g Lat (r : ℂ) := hg.symm ▸ href
  exact J0Cusps.hElkikMD_atScale hElkik hf hgp hLat hκ
    (rational_of_matching_coeffs (Ecurve ℓ) g hcoef hNC hκg hrefg)

end ZInQ.Manuscript.RC.KappaRational2
