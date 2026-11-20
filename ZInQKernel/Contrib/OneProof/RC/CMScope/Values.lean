import ZInQKernel.Contrib.OneProof.RC.CMScope.Prepared
import ZInQKernel.Contrib.OneProof.RC.ParamJoin.Assembly

/-! The two value slots at the fixed scale, tex 2411–2416 and 8213–8217.
The reuse of the existing form and evaluation interfaces is on the spot (c). -/

noncomputable section

open NumberField WeierstrassCurve ZInQ.Progressions TauCeti.GlobalNumberFields
  ZInQ.Manuscript ZInQ.Manuscript.RC.Wiring ZInQ.Manuscript.SelmerTwoPower
  ZInQ.Manuscript.RC.PreparedParam
  ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.CloudB3RC53.GenusOdd

namespace ZInQ.Manuscript.RC.CMScope

/-- The conductor-one values in the exact slot used by the (3.4) assembly. -/
theorem genus_values {ℓ : ℕ} {W : WData ℓ} (P : Prints) (hℓ : 0 < ℓ)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat)
    {κ : ℂ} (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ) (hr : ∃ c : ℚ, (c : ℂ) = κ)
    (hCM : letI : NeZero (newformLevel (Ecurve ℓ)) := ⟨(Gz34Instance.curve_form P hℓ).1.ne'⟩
           CMFieldOfDefinitionScoped (X0Branch.model (newformLevel (Ecurve ℓ))))
    (hpartner : IsGenusPartner ℓ W.hstar)
    (hlevel0 : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → p ∈ S0 ℓ) :
    ∀ h (hp : Prepared (Ecurve ℓ) W.hstar h),
      StageSelector.PreparedParamValue (Ecurve ℓ) f Lat κ (Gz34Instance.curve_form P hℓ).1
        (Gz34Instance.genusPartner_of_support hpartner hlevel0) hp := by
  let _ := Gz34Instance.curve_elliptic hℓ
  let _ : NeZero (newformLevel (Ecurve ℓ)) := ⟨(Gz34Instance.curve_form P hℓ).1.ne'⟩
  exact preparedParamValues hCM (ParamJoin.algebraicParametrizationAtScale f hf hLat hκ hr)
    (Gz34Instance.curve_form P hℓ).1 (Gz34Instance.genusPartner_of_support hpartner hlevel0)

/-- The companion's selected point lies over the ring class field of the
order of conductor `|h|`, by the same fixed modular morphism. -/
theorem ring_values {ℓ : ℕ} (P : Prints) (hℓ : 0 < ℓ)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2} {Lat : PeriodPair} {κ : ℂ}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = ((Ecurve ℓ).LFunction n : ℂ))
    (hLat : IsLatticeOf (Ecurve ℓ) Lat)
    (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ) (hr : ∃ c : ℚ, (c : ℂ) = κ)
    (hCM : letI : NeZero (newformLevel (Ecurve ℓ)) := ⟨(Gz34Instance.curve_form P hℓ).1.ne'⟩
           CMFieldOfDefinitionScoped (X0Branch.model (newformLevel (Ecurve ℓ)))) {s : ℤ} :
    ∀ h k (hp : Prepared (Ecurve ℓ) s h) (hk : Companion (Ecurve ℓ) Lat s h k),
      Gz34Instance.RingParamValue (Ecurve ℓ) f Lat κ (Gz34Instance.curve_form P hℓ).1 hp hk := by
  let _ := Gz34Instance.curve_elliptic hℓ
  have hN := (Gz34Instance.curve_form P hℓ).1
  let _ : NeZero (newformLevel (Ecurve ℓ)) := ⟨hN.ne'⟩
  intro h k hp hk
  let _ : Fact (¬ IsSquare (k : ℚ)) :=
    ⟨Qsqrt.not_isSquare_of_squarefree hk.2.2.1 (ne_of_lt (hk.1.trans zero_lt_one))⟩
  let _ : NeZero h.natAbs := ⟨Int.natAbs_ne_zero.mpr hp.1.ne'⟩
  let K := Qsqrt k
  have hD : discr K = k := StageSelector.qsqrt_discr hk.1 hk.2.2.1 hk.2.1
  obtain ⟨hNc, hNloc⟩ := Gz34Instance.companion_formConditions hp hk
  have h8 : discr K % 8 = 1 := by
    rw [hD]
    exact (hNloc 2 Nat.prime_two (dvd_mul_right 2 _)).2.1 rfl
  obtain ⟨h4, h3⟩ := discr_ne_of_mod_eight h8
  have hs : ∀ p : ℕ, p.Prime → p ∣ 2 * newformLevel (Ecurve ℓ) → SplitsIn K p := by
    intro p hp hpn
    exact Splitting.splittingCriterion_proof K Qsqrt.finrank p hp (hD.symm ▸ hNloc p hp hpn)
  have hc : h.natAbs.Coprime (2 * newformLevel (Ecurve ℓ) * (discr K).natAbs) := by
    rw [hD]
    apply Nat.coprime_of_dvd
    intro p hprime hph hp'
    rcases hprime.dvd_mul.mp hp' with hpN | hpk
    · exact (hp.2.2.1 p hprime hpN).1 (Int.natCast_dvd.mpr hph)
    · exact (hk.2.2.2.1 p hprime (dvd_mul_of_dvd_right (Int.natCast_dvd.mpr hph) _)).1
        (Int.natCast_dvd.mpr hpk)
  have hcN : IsCoprime (h.natAbs : ℤ) (newformLevel (Ecurve ℓ) : ℤ) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    change h.natAbs.Coprime (newformLevel (Ecurve ℓ))
    exact hNc.symm
  have hn : IsCoprime (discr K * (h.natAbs : ℤ) ^ 2) (newformLevel (Ecurve ℓ) : ℤ) := by
    rw [hD]
    exact (coprime_level hNloc).mul_left hcN.pow_left
  have hneg : discr K * (h.natAbs : ℤ) ^ 2 < 0 := by
    rw [hD]
    exact mul_neg_of_neg_of_pos hk.1 (pow_pos (by exact_mod_cast NeZero.pos h.natAbs) 2)
  have hO := HeegnerAnchor.conductorOrder_discr (K := K) Qsqrt.finrank h.natAbs
  let bc := (Gz34Instance.companionForm hN hp hk).val
  obtain ⟨ι, x, hx⟩ := hCM.atForm (K := K) Qsqrt.finrank (Qsqrt.isTotallyComplex hk.1) hs
    h4 h3 hc (A := (newformLevel (Ecurve ℓ) : ℤ)) (B := bc.1) (C := bc.2) hO hneg hn
    (by rw [hD]; exact (Gz34Instance.companionForm hN hp hk).property)
  obtain ⟨y, hy⟩ := value_of_cmPoint (ParamJoin.algebraicParametrizationAtScale f hf hLat hκ hr) ι x hx
  unfold Gz34Instance.RingParamValue
  refine ⟨ι, y, ?_⟩
  exact hy.trans (congrArg (fun d =>
    phiAn (Ecurve ℓ) f Lat κ (cmPoint (newformLevel (Ecurve ℓ)) bc.1 (d * (h.natAbs : ℤ) ^ 2))) hD)

/-- The existing stage setup provides positive level and the prepared selector's inputs. -/
theorem prepared_values {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W}
    {L : ℕ} (s : StageKummer.Setup I L) (hr : ∃ c : ℚ, (c : ℂ) = I.κ)
    (hCM : letI : NeZero (newformLevel (Ecurve ℓ)) := ⟨(StageKummer.positiveLevel s).ne'⟩
           CMFieldOfDefinitionScoped (X0Branch.model (newformLevel (Ecurve ℓ)))) :
    ∀ h (hp : Prepared (Ecurve ℓ) W.hstar h),
      StageSelector.PreparedParamValue (Ecurve ℓ) I.f I.Lat I.κ
        (StageKummer.positiveLevel s) I.hgp hp := by
  let _ : NeZero (newformLevel (Ecurve ℓ)) := ⟨(StageKummer.positiveLevel s).ne'⟩
  let _ := s.eE
  exact preparedParamValues hCM (ModFnClassify.curve_algebraicParametrizationAtScale I _ hr)
    (StageKummer.positiveLevel s) I.hgp

/-- The selector can fill admissible holes using the same chart and fixed scale. -/
theorem missing_values {ℓ : ℕ} {W : WData ℓ} {I : GenusOddInstance W}
    {L : ℕ} (s : StageKummer.Setup I L) (hr : ∃ c : ℚ, (c : ℂ) = I.κ)
    (hCM : letI : NeZero (newformLevel (Ecurve ℓ)) := ⟨(StageKummer.positiveLevel s).ne'⟩
           CMFieldOfDefinitionScoped (X0Branch.model (newformLevel (Ecurve ℓ)))) :
    StageKummer.MissingParamValues s := by
  let _ : NeZero (newformLevel (Ecurve ℓ)) := ⟨(StageKummer.positiveLevel s).ne'⟩
  intro D h _ _
  exact prepared_values s hr hCM D
    (I.hprep D (StageKummer.preparedGlue s h.choose D h.choose_spec))

end ZInQ.Manuscript.RC.CMScope
