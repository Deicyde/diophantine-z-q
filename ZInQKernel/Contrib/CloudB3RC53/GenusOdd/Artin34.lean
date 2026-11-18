import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.ElliotClosure
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.GlueTwo

/-!
# GenusOdd: (3.4) from the printed leaves and `ArtinFactorization` alone (PROVED)

`RingClassGalois` is no longer needed: Elliot's index-at-most-two comparison is carried out in the
normal closure of `H_c` over `ℚ` (`two_nsmul_mem_twist_add_torsion'`), and the square roots
`√d₁, √d₂ ∈ H_c` come from `genusRoots_proof`. `datum_facts_core'` and `core34'` are
`datum_facts_core` and `core34` with these inputs; `genusLower34_of_artin` is (3.4).
-/

noncomputable section

open NumberField TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  TauCeti.ClassFieldTheory IsDedekindDomain Complex

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST

open Classical in
/-- **`datum_facts_core` with `ArtinFactorization` the only GLUE** (PROVED): as `datum_facts_core`,
with `GenusRoots`, `TwistDescent`, `NeronTateTwist`, the splitting criterion proved and Elliot's
comparison taken in the normal closure (no `RingClassGalois`). For a field `K` of discriminant `D`, `χ = χ_{d₁} ∘ N` on `Pic(O_c)`, `d₁ d₂ = D c²`, a Heegner
point `y` and entire continuations `F₁, F₂` of `L(E^{(d₁)}, s)`, `L(E^{(d₂)}, s)`: if `E^{(d_T)}(ℚ)` is
torsion for the one of `d₁, d₂` called `d_T`, there is `Q` on the rational line `E^{(d_R)}(ℚ)` (the
other one) with `(F₁F₂)'(1) = C/(c√|D|) · ĥ(Q)/2` and `j(P_χ) ≤ j(Q) ≤ j(P_χ) + 1`. -/
theorem datum_facts_core' (hArtin : ArtinFactorization) {E : WeierstrassCurve ℚ} [E.IsElliptic] (h₁ : E.a₁ = 0)
    (h₃ : E.a₃ = 0)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
    {Lat : PeriodPair} {κ : ℂ} {C : ℝ} (hC : CSTFormula E f Lat κ C)
    {D : ℤ} {c : ℕ} {d₁ d₂ dR dT : ℤ} (K : Type) [Field K] [NumberField K] [NeZero c]
    (hK2 : Module.finrank ℚ K = 2) (hTC : IsTotallyComplex K) (hdisc : discr K = D)
    (χ : Pic (conductorOrder K c) →* ℂˣ) (hquad : IsQuadRingClassChar K c d₁ χ)
    (hprim : IsPrimitiveRingClassChar K c χ) (A B C' : ℤ)
    (hform : IsHeegnerForm (newformLevel E) (D * c ^ 2) A B C')
    (ι : ringClassField (conductorOrder K c) →ₐ[ℚ] ℂ)
    (y : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point)
    (hy : WeierstrassCurve.Affine.Point.map (W' := E.toAffine) ι y =
        phiAn E f Lat κ (cmPoint A B (D * c ^ 2)))
    (hprod : d₁ * d₂ = D * c ^ 2) (hd₁ : d₁ % 4 = 1) (hsq : Squarefree d₁) (hcd : (c : ℤ) ∣ d₁)
    (hcD : Nat.Coprime c D.natAbs) (hDodd : Odd D) (hD3 : D ≠ -3) (hD4 : D ≠ -4)
    (hDN : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SquareAt p D)
    (hcN : Nat.Coprime c (newformLevel E)) (hdN : Nat.Coprime (d₁ * d₂).natAbs (newformLevel E))
    (hRT : (dR = d₁ ∧ dT = d₂) ∨ (dR = d₂ ∧ dT = d₁))
    (htorT : ∀ P : (qtwist E dT).toAffine.Point, IsOfFinAddOrder P)
    {F₁ F₂ : ℂ → ℂ} (hF₁ : IsLContinuation (qtwist E d₁) F₁)
    (hF₂ : IsLContinuation (qtwist E d₂) F₂) :
    ∃ Q : (qtwist E dR).toAffine.Point,
      deriv (fun s => F₁ s * F₂ s) 1 =
        ((C / ((c : ℝ) * Real.sqrt |(D : ℝ)|) : ℝ) : ℂ) * ((Q.canonicalHeight / 2 : ℝ) : ℂ) ∧
      nativeIndex E χ y ≤ twoDivIndex ⊤ Q ∧ twoDivIndex ⊤ Q ≤ nativeIndex E χ y + 1 := by
  subst hdisc
  let _ : DecidableEq (ringClassField (conductorOrder K c)) :=
    Classical.decEq (ringClassField (conductorOrder K c))
  -- genus theory: `√d₁, √d₂ ∈ H_c` and complex conjugation
  obtain ⟨s₁, s₂, hs₁, hs₂, hσ⟩ := genusRoots_proof K hK2 hTC hDodd c d₁ d₂ hprod hd₁ hsq
    hcd hcD χ hquad
  have hd₁0 : d₁ ≠ 0 := by rintro rfl; norm_num at hd₁
  have hd₂0 : d₂ ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hprod
    have hc0 : (c : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne c)
    have hD0 : discr K ≠ 0 := by rintro h; rw [h] at hDodd; norm_num at hDodd
    exact (mul_ne_zero hD0 (pow_ne_zero 2 hc0)) hprod.symm
  have hsplit : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SplitsIn K p := fun p hp hpN =>
    ZInQ.Contrib.CloudB3RC53.Splitting.splittingCriterion_proof K hK2 p hp (hDN p hp hpN)
  have hneg12 : d₁ * d₂ < 0 := by
    rw [hprod]
    have hD : discr K < 0 := discr_neg_of_totallyComplex hK2
    have hc0 : (0 : ℤ) < (c : ℤ) ^ 2 := by
      have : (c : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne c
      positivity
    exact mul_neg_of_neg_of_pos hD hc0
  -- Cai–Shu–Tian at this datum
  have hCST := hC K hK2 hTC hD3 hD4 hsplit c hcN χ hprim A B C' hform ι y hy
    (fun s => F₁ s * F₂ s) (hF₁.1.mul hF₂.1) (fun s hs => by
      rw [hF₁.2 s hs, hF₂.2 s hs]
      exact (hArtin E K hK2 hTC hDodd hsplit c d₁ d₂ hprod hd₁ hsq hcd hcD hdN χ hquad s hs).symm)
  rw [heightK_eq_canonicalHeight E hquad.1 y] at hCST
  have hP : heegnerSum E χ y ∈ eigenLattice E χ := heegnerSum_mem_eigenLattice E hquad.1 y
  have hn : 0 < Module.finrank K (ringClassField (conductorOrder K c)) := Module.finrank_pos
  have htower : Module.finrank ℚ (ringClassField (conductorOrder K c)) =
      2 * Module.finrank K (ringClassField (conductorOrder K c)) := by
    rw [← Module.finrank_mul_finrank ℚ K, hK2]
  have finish : ∀ (dR' dT' : ℤ) (sR sT : ringClassField (conductorOrder K c)),
      sR ^ 2 = (dR' : ringClassField (conductorOrder K c)) →
      sT ^ 2 = (dT' : ringClassField (conductorOrder K c)) → dR' ≠ 0 → dT' ≠ 0 →
      (∀ σ : ringClassField (conductorOrder K c) ≃ₐ[K] ringClassField (conductorOrder K c),
        σ sR = (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : ℤ) * sR ∧
        σ sT = (chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) : ℤ) * sT) →
      dR' * dT' < 0 →
      (∀ P : (qtwist E dT').toAffine.Point, IsOfFinAddOrder P) →
      ∃ Q : (qtwist E dR').toAffine.Point,
        deriv (fun s => F₁ s * F₂ s) 1 =
          ((C / ((c : ℝ) * Real.sqrt |(discr K : ℝ)|) : ℝ) : ℂ) *
            ((Q.canonicalHeight / 2 : ℝ) : ℂ) ∧
        nativeIndex E χ y ≤ twoDivIndex ⊤ Q ∧ twoDivIndex ⊤ Q ≤ nativeIndex E χ y + 1 := by
    intro dR' dT' sR sT hsR hsT hdR hdT hσ' hneg' htor'
    have hcast : ∀ d : ℤ, ((d : ringClassField (conductorOrder K c))) =
        algebraMap ℚ (ringClassField (conductorOrder K c)) (d : ℚ) := fun d => by
      rw [map_intCast]
    have hne : ∀ {d : ℤ} {s : ringClassField (conductorOrder K c)},
        s ^ 2 = (d : ringClassField (conductorOrder K c)) → d ≠ 0 → s ≠ 0 := by
      intro d s hs hd h0
      rw [h0] at hs
      have : ((d : ringClassField (conductorOrder K c))) = 0 := by rw [← hs]; ring
      exact hd (by exact_mod_cast this)
    have hsR0 := hne hsR hdR
    have hsT0 := hne hsT hdT
    have hsRd : sR ^ 2 = algebraMap ℚ _ (dR' : ℚ) := by rw [hsR, hcast]
    have hsTd : sT ^ 2 = algebraMap ℚ _ (dT' : ℚ) := by rw [hsT, hcast]
    have helliot := two_nsmul_mem_twist_add_torsion' E h₁ h₃ hK2 hsR0 hsRd hsT0 hsTd
      (by exact_mod_cast hneg') hσ' htor'
    obtain ⟨Q, hQ⟩ := helliot _ hP
    refine ⟨Q, ?_, ?_⟩
    · have hsqH : ∀ (m : ℕ) (x : (E.baseChange (ringClassField (conductorOrder K c))).toAffine.Point),
          ((m • x).canonicalHeight) = (m : ℝ) ^ 2 * x.canonicalHeight :=
        fun m x => WeierstrassCurve.Affine.Point.canonicalHeight_nsmul m x
      have h2P := height_add_torsion hsqH
        (twistEmb E dR' sR (twistVC_smul E h₁ h₃ hsR0 hsRd) Q) _ hQ
      rw [add_sub_cancel, hsqH, neronTateTwist_proof E h₁ h₃ (dR' : ℚ) _ sR hsR0 hsRd Q, htower] at h2P
      have hn' : (Module.finrank K (ringClassField (conductorOrder K c)) : ℝ) ≠ 0 := by
        exact_mod_cast hn.ne'
      push_cast at h2P
      have key : ((Module.finrank K (ringClassField (conductorOrder K c)) : ℝ))⁻¹ *
          (heegnerSum E χ y).canonicalHeight = Q.canonicalHeight / 2 := by
        rw [show (heegnerSum E χ y).canonicalHeight = 2 * (Module.finrank K
            (ringClassField (conductorOrder K c)) : ℝ) * Q.canonicalHeight / 4 by linarith]
        field_simp
        ring
      rw [hCST, key]
    · have hψM : ∀ r, twistEmb E dR' sR (twistVC_smul E h₁ h₃ hsR0 hsRd) r ∈ eigenLattice E χ := by
        intro r σ
        have hsRne : sR ≠ -sR := fun h => hsR0 (by
          have : (2 : ringClassField (conductorOrder K c)) * sR = 0 := by linear_combination h
          simpa using this)
        have hcs : chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) = 1 ∨
            chiSign χ ((ringClassArtinEquiv (conductorOrder K c)).symm σ) = -1 := by
          unfold chiSign; split_ifs <;> simp
        have hs := (hσ' σ).1
        show galPt E σ _ = _
        rcases hcs with h | h
        · rw [h] at hs
          have hσs : σ sR = sR := by rw [hs]; simp
          rw [galPt, map_twistEmb_eq_ite E h₁ h₃ (dR' : ℚ) (σ.toAlgHom.restrictScalars ℚ) hsR0
            hsRd (Or.inl hσs) r, if_pos (by exact hσs), h, one_smul]
        · rw [h] at hs
          have hσs : σ sR = -sR := by rw [hs]; simp
          have hσs' : ¬ σ sR = sR := fun h' => hsRne (h'.symm.trans hσs)
          rw [galPt, map_twistEmb_eq_ite E h₁ h₃ (dR' : ℚ) (σ.toAlgHom.restrictScalars ℚ) hsR0
            hsRd (Or.inr hσs) r, if_neg (by exact hσs'), h, neg_smul, one_smul]
      have := twoDivIndex_transfer _ (twistEmb_injective E (dR' : ℚ) sR _) (eigenLattice E χ) hψM
        helliot hP hQ
      exact this
  rcases hRT with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · subst e1 e2
    exact finish _ _ s₁ s₂ hs₁ hs₂ hd₁0 hd₂0 hσ hneg12 htorT
  · subst e1 e2
    exact finish _ _ s₂ s₁ hs₂ hs₁ hd₂0 hd₁0 (fun σ => ⟨(hσ σ).2, (hσ σ).1⟩)
      (by rw [mul_comm]; exact hneg12) htorT

/-- **`core34` with `ArtinFactorization` the only GLUE** (PROVED from `Prints` and `Glue34`). -/
theorem core34' (P : Prints) (hArtin : ArtinFactorization) {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (h₁ : E.a₁ = 0) (h₃ : E.a₃ = 0)
    {f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel E) : Subgroup (GL (Fin 2) ℝ)) 2}
    (hf : ∀ n : ℕ, 0 < n → (UpperHalfPlane.qExpansion 1 f).coeff n = (E.LFunction n : ℂ))
    {Lat : PeriodPair} (hLat : IsLatticeOf E Lat) (hNC : IsNonCMLattice Lat) {κ : ℂ}
    (hκ : IsParamScale (newformLevel E) f Lat κ) {hstar : ℤ} (hgp : GenusPartner E hstar)
    (hMD : ∃ q : ℚ, (q : ℂ) = Lstar E Lat hstar) {h k' : ℤ} (hp : Prepared E hstar h)
    (hz : AnalyticRank (qtwist E h) 1) (hk : Companion E Lat hstar h k')
    (datG : HeegnerDatum E f Lat κ (h * hstar) 1 hstar)
    (datR : HeegnerDatum E f Lat κ k' h.natAbs h) :
    datG.index ≠ ⊤ ∧ datR.index ≠ ⊤ ∧ ∃ ε : ℤ, |ε| ≤ 2 ∧
      2 * (datR.index.toNat : ℤ) - 2 * (datG.index.toNat : ℤ) =
        padicValRat 2 (LstarQ E Lat (h * k')) - padicValRat 2 (LstarQ E Lat hstar) + ε := by
  obtain ⟨C, hC0, hC⟩ := cst_formula P E f hf Lat hLat hNC κ hκ
  obtain ⟨h0, hsqh, hsqp, hcop⟩ := hp
  obtain ⟨hs0, hs4, hssq, hs5, hsp, har0⟩ := hgp
  obtain ⟨k0, k4, ksq, kp, kcop, hL⟩ := hk
  have hN2 : ∀ p : ℕ, p ∣ newformLevel E → p ∣ 2 * newformLevel E :=
    fun p hp => dvd_mul_of_dvd_right hp 2
  have h2h : SquareAt 2 h := hsqp 2 Nat.prime_two (dvd_mul_right 2 _)
  have h2k : SquareAt 2 k' := kp 2 Nat.prime_two (by
    push_cast; exact dvd_mul_of_dvd_left (dvd_mul_right 2 _) h)
  have h2s : SquareAt 2 hstar := hsp 2 Nat.prime_two (dvd_mul_right 2 _)
  have h8 : h % 8 = 1 := h2h.2.1 rfl
  have s8 : hstar % 8 = 1 := h2s.2.1 rfl
  have k8 : k' % 8 = 1 := h2k.2.1 rfl
  have hDg4 : 4 < |h * hstar| := by rw [abs_mul, abs_of_pos h0]; nlinarith [abs_nonneg hstar]
  -- ranks
  have hh0 : (h : ℚ) ≠ 0 := by exact_mod_cast h0.ne'
  have hs0' : (hstar : ℚ) ≠ 0 := by exact_mod_cast hs0.ne
  have hk0' : ((h * k' : ℤ) : ℚ) ≠ 0 := by
    have : h * k' ≠ 0 := mul_ne_zero h0.ne' k0.ne
    exact_mod_cast this
  have hEh : (qtwist E h).IsElliptic := qtwist_isElliptic E hh0
  have hrank1 : Module.rank ℤ (qtwist E h).toAffine.Point = 1 := by
    have := (P.kolyvagin (qtwist E h) hEh (P.bcdt _ hEh) 1 le_rfl hz).1
    exact_mod_cast this
  have htorS : ∀ Q : (qtwist E hstar).toAffine.Point, IsOfFinAddOrder Q := by
    have hE := qtwist_isElliptic E hs0'
    have := (P.kolyvagin (qtwist E hstar) hE (P.bcdt _ hE) 0 (by norm_num) har0).1
    exact torsion_of_rank_zero (by exact_mod_cast this)
  -- `L(E^{(hk')}, 1) ≠ 0` and `Ω⁻ ≠ 0`, from `L_*(hk') ≠ 0`
  have hΩ : (omegaMinus Lat : ℂ) ≠ 0 := by
    intro h0'; apply hL; unfold Lstar; rw [h0', div_zero]
  have hLk : Lval (qtwist E (h * k' : ℤ)) ≠ 0 := by
    intro h0'; apply hL; unfold Lstar; rw [h0', mul_zero, zero_div]
  have hark := analyticRank_zero_of_Lval_ne_zero hLk
  have htorK : ∀ Q : (qtwist E (h * k' : ℤ)).toAffine.Point, IsOfFinAddOrder Q := by
    have hE := qtwist_isElliptic E hk0'
    have := (P.kolyvagin (qtwist E (h * k' : ℤ)) hE (P.bcdt _ hE) 0 (by norm_num) hark).1
    exact torsion_of_rank_zero (by exact_mod_cast this)
  -- continuations
  obtain ⟨Fh, hFh, hFh1, hFh'⟩ := analyticRank_one hz
  obtain ⟨Fs, hFs, hFs1⟩ := analyticRank_zero_iff.mp har0
  obtain ⟨Fk, hFk, hFk1⟩ := analyticRank_zero_iff.mp hark
  -- square classes
  have hsqDg : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SquareAt p (h * hstar) := fun p hp hpN =>
    (hsqp p hp (hN2 p hpN)).mul (hsp p hp (hN2 p hpN)) hp
  have hsqDr : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SquareAt p k' := fun p hp hpN =>
    kp p hp (dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (by exact_mod_cast hpN) 2) h)
  have hsqhN : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SquareAt p h := fun p hp hpN => hsqp p hp (hN2 p hpN)
  have hsqsN : ∀ p : ℕ, p.Prime → p ∣ newformLevel E → SquareAt p hstar := fun p hp hpN => hsp p hp (hN2 p hpN)
  have habs : (h.natAbs : ℤ) = h := by rw [Int.natCast_natAbs, abs_of_pos h0]
  -- the genus datum: `D = h h_*`, `c = 1`, `d₁ = h_*`, `d₂ = h`
  obtain ⟨Qg, hderG, hjG1, hjG2⟩ := by
    letI := datG.field; letI := datG.nf; letI := datG.nz
    exact datum_facts_core' hArtin h₁ h₃ hC datG.K datG.finrank_two datG.totallyComplex datG.disc
      datG.χ datG.quad datG.prim datG.A datG.B datG.C datG.form datG.ι datG.y datG.hy
      (d₂ := h) (dR := h) (dT := hstar) (by push_cast; ring) hs4 hssq (by simp)
      (Nat.coprime_one_left _) (Int.odd_iff.mpr (by
        rw [Int.mul_emod, show h % 2 = 1 by omega, show hstar % 2 = 1 by omega]; norm_num))
      (by intro hD; rw [hD] at hDg4; norm_num at hDg4)
      (by intro hD; rw [hD] at hDg4; norm_num at hDg4)
      hsqDg (Nat.coprime_one_left _)
      (coprime_of_squareAt fun p hp hpN => (hsqsN p hp hpN).mul (hsqhN p hp hpN) hp)
      (Or.inr ⟨rfl, rfl⟩) htorS hFs hFh
  -- the ring-class datum: `D = k'`, `c = |h|`, `d₁ = h`, `d₂ = h k'`
  have hcopHK : Nat.Coprime h.natAbs k'.natAbs := by
    refine Nat.coprime_of_dvd fun p hp hph hpk => (kp p hp ?_).1 (Int.natCast_dvd.mpr hpk)
    exact dvd_mul_of_dvd_right (Int.natCast_dvd.mpr hph) _
  obtain ⟨Qr, hderR, hjR1, hjR2⟩ := by
    letI := datR.field; letI := datR.nf; letI := datR.nz
    exact datum_facts_core' hArtin h₁ h₃ hC datR.K datR.finrank_two datR.totallyComplex datR.disc
      datR.χ datR.quad datR.prim datR.A datR.B datR.C datR.form datR.ι datR.y datR.hy
      (d₂ := h * k') (dR := h) (dT := h * k') (by rw [habs]; ring) (h2h.mod_four) hsqh
      (by rw [habs]) hcopHK (h2k.odd) (by intro hD; rw [hD] at k8; norm_num at k8)
      (by intro hD; rw [hD] at k8; norm_num at k8) hsqDr
      (coprime_of_squareAt hsqhN)
      (coprime_of_squareAt fun p hp hpN => (hsqhN p hp hpN).mul
        ((hsqhN p hp hpN).mul (hsqDr p hp hpN) hp) hp)
      (Or.inl ⟨rfl, rfl⟩) htorK hFh hFk
  -- the two derivatives
  have dG : deriv (fun s => Fs s * Fh s) 1 = Fs 1 * deriv Fh 1 := by
    rw [show (fun s => Fs s * Fh s) = Fs * Fh from rfl, deriv_mul (hFs.1 1) (hFh.1 1), hFh1]; ring
  have dR : deriv (fun s => Fh s * Fk s) 1 = deriv Fh 1 * Fk 1 := by
    rw [show (fun s => Fh s * Fk s) = Fh * Fk from rfl, deriv_mul (hFh.1 1) (hFk.1 1), hFh1]; ring
  rw [dG] at hderG
  rw [dR] at hderR
  -- the real square roots
  have hhR : (0 : ℝ) < h := by exact_mod_cast h0
  set a := Real.sqrt (h : ℝ) with ha
  set b := Real.sqrt |(k' : ℝ)| with hb
  set e := Real.sqrt |(hstar : ℝ)| with he
  have ha0 : 0 < a := Real.sqrt_pos.mpr hhR
  have hb0 : 0 < b := Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast k0.ne))
  have he0 : 0 < e := Real.sqrt_pos.mpr (abs_pos.mpr (by exact_mod_cast hs0.ne))
  have ha2 : a ^ 2 = h := Real.sq_sqrt hhR.le
  have hsg : Real.sqrt |((h * hstar : ℤ) : ℝ)| = a * e := by
    push_cast; rw [abs_mul, abs_of_pos hhR, Real.sqrt_mul hhR.le]
  have hsk : Real.sqrt |((h * k' : ℤ) : ℝ)| = a * b := by
    push_cast; rw [abs_mul, abs_of_pos hhR, Real.sqrt_mul hhR.le]
  have hnat : ((h.natAbs : ℕ) : ℝ) = h := by
    rw [Nat.cast_natAbs, abs_of_pos h0]
  rw [hsg] at hderG
  rw [hnat] at hderR
  -- heights are nonzero
  have hDh := hFh'
  have hXs := hFs1
  have hYk := hFk1
  have hg0 : Qg.canonicalHeight ≠ 0 := by
    intro h0'
    rw [h0', zero_div, Complex.ofReal_zero, mul_zero] at hderG
    exact mul_ne_zero hXs hDh hderG
  have hr0 : Qr.canonicalHeight ≠ 0 := by
    intro h0'
    rw [h0', zero_div, Complex.ofReal_zero, mul_zero] at hderR
    exact mul_ne_zero hDh hYk hderR
  -- the rank-one comparison on `E^{(h)}(ℚ)`
  have hsqZ : ∀ (n : ℤ) (x : (qtwist E h).toAffine.Point),
      (n • x).canonicalHeight = (n : ℝ) ^ 2 * x.canonicalHeight :=
    fun n x => WeierstrassCurve.Affine.Point.canonicalHeight_zsmul n x
  have hsqN : ∀ (n : ℕ) (x : (qtwist E h).toAffine.Point),
      (n • x).canonicalHeight = (n : ℝ) ^ 2 * x.canonicalHeight :=
    fun n x => WeierstrassCurve.Affine.Point.canonicalHeight_nsmul n x
  have hfinB : ∀ B : ℝ, {x : (qtwist E h).toAffine.Point | x.canonicalHeight ≤ B}.Finite :=
    fun B => Northcott.finite_le (h := WeierstrassCurve.Affine.Point.canonicalHeight) B
  have hpos : ∀ Q : (qtwist E h).toAffine.Point, Q.canonicalHeight ≠ 0 →
      0 < Q.canonicalHeight := fun Q hQ =>
    lt_of_le_of_ne (WeierstrassCurve.Affine.Point.canonicalHeight_nonneg Q) (Ne.symm hQ)
  have hnt : ∀ Q : (qtwist E h).toAffine.Point, Q.canonicalHeight ≠ 0 → ¬ IsOfFinAddOrder Q :=
    fun Q hQ ht => hQ (WeierstrassCurve.Affine.Point.canonicalHeight_eq_zero_of_isOfFinAddOrder ht)
  have hJg := twoDivIndex_ne_top hsqN hfinB (hpos Qg hg0)
  have hJr := twoDivIndex_ne_top hsqN hfinB (hpos Qr hr0)
  obtain ⟨q, hq0, hqeq, hqv⟩ := rank_one_ratio hsqZ (exists_dep_of_rank_le_one (le_of_eq hrank1))
    (hnt Qr hr0) (hnt Qg hg0) hJr hJg
  -- `L_*(hk') = q² L_*(h_*)`
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  have hec : (e : ℂ) ≠ 0 := by exact_mod_cast he0.ne'
  have hhc : (h : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  have ha2c : (a : ℂ) ^ 2 = h := by exact_mod_cast ha2
  have E1 := hderG
  have E2 := hderR
  rw [hqeq] at E2
  push_cast at E1 E2
  have key : ((a : ℂ) * b * Fk 1 - (q : ℂ) ^ 2 * (e * Fs 1)) * deriv Fh 1 = 0 := by
    calc ((a : ℂ) * b * Fk 1 - (q : ℂ) ^ 2 * (e * Fs 1)) * deriv Fh 1
        = (a : ℂ) * b * (deriv Fh 1 * Fk 1) - (q : ℂ) ^ 2 * e * (Fs 1 * deriv Fh 1) := by ring
      _ = (a : ℂ) * b * ((C : ℂ) / ((h : ℂ) * b) * ((q : ℂ) ^ 2 * Qg.canonicalHeight / 2)) -
          (q : ℂ) ^ 2 * e * ((C : ℂ) / (1 * ((a : ℂ) * e)) * (Qg.canonicalHeight / 2)) := by
        rw [E1, E2]
      _ = (C : ℂ) * (q : ℂ) ^ 2 * Qg.canonicalHeight * ((a : ℂ) ^ 2 - h) / (2 * h * a) := by
        field_simp
      _ = 0 := by rw [ha2c, sub_self, mul_zero, zero_div]
  have key' : (a : ℂ) * b * Fk 1 = (q : ℂ) ^ 2 * (e * Fs 1) :=
    sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_right hDh)
  have hLs : Lstar E Lat (h * k') = (q : ℂ) ^ 2 * Lstar E Lat hstar := by
    unfold Lstar
    rw [Lval_eq hFk, Lval_eq hFs, hsk, ← he]
    push_cast
    rw [key']
    ring
  obtain ⟨qs, hqs⟩ := hMD
  have hLsq : ((q ^ 2 * qs : ℚ) : ℂ) = Lstar E Lat (h * k') := by
    rw [hLs, ← hqs]; push_cast; ring
  have hqs0 : qs ≠ 0 := by
    intro h0'
    rw [h0', Rat.cast_zero] at hqs
    unfold Lstar at hqs
    rw [Lval_eq hFs, ← he] at hqs
    exact (div_ne_zero (mul_ne_zero hec hXs) hΩ) hqs.symm
  rw [LstarQ_eq hLsq, LstarQ_eq hqs]
  have := Fact.mk Nat.prime_two
  rw [padicValRat.mul (pow_ne_zero 2 hq0) hqs0, padicValRat.pow q]
  -- the index valuations
  have hjG1' : datG.index ≤ twoDivIndex ⊤ Qg := hjG1
  have hjG2' : twoDivIndex ⊤ Qg ≤ datG.index + 1 := hjG2
  have hjR1' : datR.index ≤ twoDivIndex ⊤ Qr := hjR1
  have hjR2' : twoDivIndex ⊤ Qr ≤ datR.index + 1 := hjR2
  obtain ⟨JG, hJG⟩ := ENat.ne_top_iff_exists.mp hJg
  obtain ⟨JR, hJR⟩ := ENat.ne_top_iff_exists.mp hJr
  rw [← hJG] at hjG1' hjG2' hqv
  rw [← hJR] at hjR1' hjR2' hqv
  have hgT : datG.index ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top JG) hjG1'
  have hrT : datR.index ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top JR) hjR1'
  obtain ⟨jg, hjg⟩ := ENat.ne_top_iff_exists.mp hgT
  obtain ⟨jr, hjr⟩ := ENat.ne_top_iff_exists.mp hrT
  rw [← hjg] at hjG1' hjG2' ⊢
  rw [← hjr] at hjR1' hjR2' ⊢
  have a1 : jg ≤ JG := by exact_mod_cast hjG1'
  have a2 : JG ≤ jg + 1 := by exact_mod_cast hjG2'
  have a3 : jr ≤ JR := by exact_mod_cast hjR1'
  have a4 : JR ≤ jr + 1 := by exact_mod_cast hjR2'
  simp only [ENat.toNat_natCast] at hqv ⊢
  refine ⟨ENat.natCast_ne_top jg, ENat.natCast_ne_top jr, 2 * ((JG : ℤ) - jg) - 2 * ((JR : ℤ) - jr),
    abs_le.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [hqv]
  push_cast
  ring


/-- **(3.4)** (Proposition `ex:sec7-genus-lower`, tex L2418–2439) from the printed leaves and the
GLUE `ArtinFactorization` alone (PROVED). -/
theorem genusLower34_of_artin (P : Prints) (hArtin : ArtinFactorization) : GenusLower34 := by
  intro E _ h₁ h₃ f hf Lat hLat hNC κ hκ hstar hgp hElkikMD h k' hp hz hk datG datR
  exact core34' P hArtin h₁ h₃ hf hLat hNC hκ hgp hElkikMD hp hz hk datG datR

end ZInQ.Contrib.CloudB3RC53.GenusOdd
