import ZInQKernel.Contrib.GZTheta.ALArith

/-!
# atkin-li: Atkin–Li's twist theorem from strong multiplicity one

Task atkin-li. `atkinLiTwistNew_of_newformUniqueAcrossLevels : NewformUniqueAcrossLevels →
AtkinLiTwistNew`: twisting a newform `g` of level `M` (weight 2, trivial nebentypus) by `(·/r)`,
`r ≡ 1 (mod 4)` squarefree prime to `M`, gives a form new at level `N = M r²`.

Let `h = g ⊗ (·/r)` and `g'` its associated newform, of level `M' ∣ N`.
1. (twist back) The newform attached to `g' ⊗ (·/r)` has the eigenvalues of `g`, so by strong
   multiplicity one it is `g`, of level `M ∣ M' r²`: the primes of `N/M'` divide `r`.
2. `h = ∑_{e ∣ N/M'} c_e g'(eτ)` (`ALRep.lean`), and the Fricke involutions of `h` (`ALFricke.lean`)
   and of `g'` give `κ h = c_{g'} ∑_e c_e (P/e)² g'((P/e)τ)`, `P = N/M'`.
3. `ALArith.lean` gives `M' = N`; multiplicity one at level `N` gives `h = g'`, which is new.
-/

open Complex Filter ModularForm CongruenceSubgroup HeckeRing.GL2 Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped Real Topology MatrixGroups

noncomputable section

namespace ZInQ.GZTheta

open ZInQ.Contrib.HeckeFE ZInQ.GZDecomp

/-! ### The Fricke involution on `∑_e c_e g'(eτ)` -/

theorem fricke_sum {M' : ℕ} [NeZero M'] (g' : Newform M' 2) {cg : ℂ}
    (hcg : ∀ (z : ℂ) (hz : 0 < z.im) (hz' : 0 < (-1 / ((M' : ℂ) * z)).im),
      g'.toCuspForm ⟨-1 / ((M' : ℂ) * z), hz'⟩ = cg * z ^ 2 * g'.toCuspForm ⟨z, hz⟩)
    {P : ℕ} (hP : P ≠ 0) (c : ℕ → ℂ) (τ : ℍ)
    (hw : 0 < (-1 / (((M' * P : ℕ) : ℂ) * τ)).im) :
    ∑ e ∈ P.divisors, c e * gAt g'.toCuspForm e ⟨-1 / (((M' * P : ℕ) : ℂ) * τ), hw⟩ =
      cg * (τ : ℂ) ^ 2 * ∑ e ∈ P.divisors,
        c e * (((P / e : ℕ) : ℂ) ^ 2 * gAt g'.toCuspForm (P / e) τ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  have he0 := Nat.pos_of_mem_divisors he
  have heP : e ∣ P := Nat.dvd_of_mem_divisors he
  have hj : 0 < P / e := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) heP) he0
  rw [gAt, dif_pos he0, gAt, dif_pos hj]
  have hcast : (M' : ℂ) * ((P / e : ℕ) : ℂ) * (e : ℂ) = ((M' * P : ℕ) : ℂ) := by
    have : M' * (P / e) * e = M' * P := by rw [mul_assoc, Nat.div_mul_cancel heP]
    exact_mod_cast this
  have hpt : ((e : ℕ) : ℂ) * ((⟨-1 / (((M' * P : ℕ) : ℂ) * τ), hw⟩ : ℍ) : ℂ) =
      -1 / ((M' : ℂ) * (((P / e : ℕ) : ℂ) * τ)) := by
    simp only [UpperHalfPlane.coe_mk]
    have he0' : (e : ℂ) ≠ 0 := by exact_mod_cast he0.ne'
    rw [← hcast]
    field_simp
  have hz' : 0 < (-1 / ((M' : ℂ) * (((P / e : ℕ) : ℂ) * τ))).im := by
    rw [← hpt]; exact mul_im_pos_of_nat he0 _
  have := hcg (((P / e : ℕ) : ℂ) * τ) (mul_im_pos_of_nat hj τ) hz'
  rw [show (⟨((e : ℕ) : ℂ) * ((⟨-1 / (((M' * P : ℕ) : ℂ) * τ), hw⟩ : ℍ) : ℂ),
      mul_im_pos_of_nat he0 _⟩ : ℍ) = ⟨-1 / ((M' : ℂ) * (((P / e : ℕ) : ℂ) * τ)), hz'⟩ from
    UpperHalfPlane.ext hpt, this]
  ring

/-- From the function identity to the coefficient identity. -/
theorem coeff_of_fun_identity {N : ℕ} [NeZero N] (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2)
    {M' : ℕ} [NeZero M'] (g' : Newform M' 2) {P : ℕ} (hP : P ≠ 0) (c : ℕ → ℂ) {κ cg : ℂ}
    (hκ : κ ≠ 0)
    (hfi : ∀ τ : ℍ, κ * F τ = cg * ∑ e ∈ P.divisors,
      c e * (((P / e : ℕ) : ℂ) ^ 2 * gAt g'.toCuspForm (P / e) τ)) (m : ℕ) :
    κ * (qExpansion 1 F).coeff m = cg * ∑ e ∈ P.divisors,
      c e * ((((P / e) : ℕ) : ℂ) ^ 2 * Bs (coeff g') (P / e) m) := by
  have hjpos : ∀ e ∈ P.divisors, 0 < P / e := fun e he =>
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hP) (Nat.dvd_of_mem_divisors he))
      (Nat.pos_of_mem_divisors he)
  have key : ∀ τ : ℍ, HasSum (fun m : ℕ => ((cg * ∑ e ∈ P.divisors, c e *
      (((P / e : ℕ) : ℂ) ^ 2 * Bs (coeff g') (P / e) m)) / κ) •
        Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ) := by
    intro τ
    have hR : HasSum (fun m : ℕ => ∑ e ∈ P.divisors, c e *
        (((P / e : ℕ) : ℂ) ^ 2 * ((if P / e ∣ m then coeff g' (m / (P / e)) else 0) *
          Function.Periodic.qParam 1 (τ : ℂ) ^ m)))
        (∑ e ∈ P.divisors, c e * (((P / e : ℕ) : ℂ) ^ 2 * gAt g'.toCuspForm (P / e) τ)) :=
      hasSum_sum fun e he => by
        rw [gAt, dif_pos (hjpos e he)]
        exact ((hasSum_scaled g'.toCuspForm (hjpos e he) τ).mul_left _).mul_left _
    have h2 := (hR.mul_left cg).div_const κ
    rw [← hfi τ, mul_div_cancel_left₀ _ hκ] at h2
    refine h2.congr_fun fun m => ?_
    simp only [smul_eq_mul, Finset.mul_sum, Finset.sum_div, Finset.sum_mul, Bs]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  have := ModularFormClass.qExpansion_coeff_unique one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map _) key m
  rw [← this]
  field_simp

/-! ### Atkin–Li -/

theorem jacobiSym_prime_pow_eq_zero {r p : ℕ} [NeZero r] (hp : p.Prime) (hpr : p ∣ r) {j : ℕ} (hj : 1 ≤ j) :
    jacobiSym ((p ^ j : ℕ) : ℤ) r = 0 := by
  rw [jacobiSym.eq_zero_iff_not_coprime]
  intro h
  have : Nat.Coprime (p ^ j) r := by
    have h' : Int.gcd ((p ^ j : ℕ) : ℤ) (r : ℤ) = 1 := h
    rwa [Int.gcd_natCast_natCast] at h'
  have := Nat.Coprime.coprime_dvd_left (dvd_pow_self p (by omega)) this
  exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd this hpr)

/-- **Atkin–Li's twist theorem, from strong multiplicity one across levels.** -/
theorem atkinLiTwistNew_of_newformUniqueAcrossLevels (hU : NewformUniqueAcrossLevels) :
    AtkinLiTwistNew := by
  intro M _ g hχ r _ hr4 hsq hcop
  show twistJ g r ∈ TauCeti.cuspFormsNew (M * r ^ 2) 2
  have hodd : Odd r := odd_of_mod_four hr4
  have hcop' : Nat.Coprime M r := hcop.symm
  set N := M * r ^ 2 with hN
  have hN0 : N ≠ 0 := NeZero.ne N
  set H : ℕ → ℂ := fun n => (qExpansion 1 (twistJ g r)).coeff n with hH
  have hHf : ∀ n, H n = (jacobiSym n r : ℂ) * coeff g n := qExpansion_twistJ_coeff g r
  -- the eigenform `h` and its newform `g'`
  obtain ⟨E, hE, hEχ⟩ := exists_eigenformAway_twist g hχ r
  obtain ⟨M', hM'0, hM'N, g', hg'χ, hg'ev⟩ :=
    Newform.exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul
      E.mem_charSpace E.ne_zero (a := fun p hp hpN => E.eigenvalue ⟨p, hp.pos⟩ hpN)
      (fun p hp hpN => E.heckeTCuspNat_eq_eigenvalue_smul hp hpN)
  have hg1 : g'.χ = 1 := by
    rw [hEχ] at hg'χ
    ext u
    obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective hM'N u
    have := congrArg (fun φ => ((φ v : ℂˣ) : ℂ)) hg'χ
    simpa using this
  have hE1 : (qExpansion 1 E.toCuspForm).coeff 1 = 1 := by rw [hE]; exact twistJ_coeff_one g r
  -- the coefficients of `g'` at the good primes
  have hgood : ∀ p : ℕ, p.Prime → Nat.Coprime p N → coeff g' p = H p := by
    intro p hp hpN
    have e1 := g'.qExpansion_coeff_eq_eigenvalue g'.isNorm ⟨p, hp.pos⟩
      (hpN.coprime_dvd_right hM'N)
    have e2 := E.qExpansion_coeff_eq_eigenvalue hE1 ⟨p, hp.pos⟩ hpN
    rw [hE] at e2
    change coeff g' p = _ at e1
    rw [e1, hg'ev p hp hpN]
    exact e2.symm
  -- (1) twist back: `M ∣ M' r²`
  have hMdvd : M ∣ M' * r ^ 2 := by
    obtain ⟨E', hE', hE'χ⟩ := exists_eigenformAway_twist g' hg1 r
    obtain ⟨M'', hM''0, hM''L, g'', hg''χ, hg''ev⟩ :=
      Newform.exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul
        E'.mem_charSpace E'.ne_zero (a := fun p hp hpN => E'.eigenvalue ⟨p, hp.pos⟩ hpN)
        (fun p hp hpN => E'.heckeTCuspNat_eq_eigenvalue_smul hp hpN)
    have hg''1 : g''.χ = 1 := by
      rw [hE'χ] at hg''χ
      ext u
      obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective hM''L u
      have := congrArg (fun φ => ((φ v : ℂˣ) : ℂ)) hg''χ
      simpa using this
    have hE'1 : (qExpansion 1 E'.toCuspForm).coeff 1 = 1 := by
      rw [hE']; exact twistJ_coeff_one g' r
    have : NeZero (M * (M' * r ^ 2)) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne _)⟩
    have hM0 : M ∣ M * (M' * r ^ 2) := dvd_mul_right _ _
    have hM''0' : M'' ∣ M * (M' * r ^ 2) := dvd_mul_of_dvd_right hM''L M
    obtain ⟨hMM, -⟩ := hU (M * (M' * r ^ 2)) 2 M M'' 1 g g'' hM0 hM''0'
      (by rw [hχ, MonoidHom.one_comp]) (by rw [hg''1, MonoidHom.one_comp])
      (fun p hp hpN => by
        have hpM : Nat.Coprime p M := hpN.coprime_dvd_right hM0
        have hpL : Nat.Coprime p (M' * r ^ 2) := hpN.coprime_dvd_right (dvd_mul_left _ _)
        have hpr : Nat.Coprime p r :=
          hpL.coprime_dvd_right ((dvd_pow_self r two_ne_zero).mul_left M')
        have hpN' : Nat.Coprime p N := Nat.Coprime.mul_right hpM (Nat.Coprime.pow_right 2 hpr)
        have e1 := g.qExpansion_coeff_eq_eigenvalue g.isNorm ⟨p, hp.pos⟩ hpM
        have e2 := g''.qExpansion_coeff_eq_eigenvalue g''.isNorm ⟨p, hp.pos⟩
          (hpN.coprime_dvd_right hM''0')
        have e3 := E'.qExpansion_coeff_eq_eigenvalue hE'1 ⟨p, hp.pos⟩ hpL
        rw [hE', qExpansion_twistJ_coeff] at e3
        simp only [PNat.mk_coe] at e3
        rw [← e1, ← e2]
        change coeff g p = coeff g'' p
        have e4 : coeff g'' p = E'.eigenvalue ⟨p, hp.pos⟩ hpL := by
          rw [← hg''ev p hp hpL]; exact e2
        rw [e4, ← e3, hgood p hp hpN', hHf, ← mul_assoc, ← pow_two,
          jacobiSym_sq_of_coprime hpr, one_mul])
    rw [hMM]; exact hM''L
  -- the primes of `N/M'` divide `r`
  have hM0 : M ≠ 0 := NeZero.ne M
  have hr0 : r ≠ 0 := NeZero.ne r
  have hM'0' : M' ≠ 0 := NeZero.ne M'
  have hPr : ∀ p : ℕ, p.Prime → p ∣ N / M' → p ∣ r := by
    intro p hp hpP
    by_contra hpr
    have hP0 : N / M' ≠ 0 := by
      intro h0; rw [Nat.div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · exact hM'0' h0
      · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hM'N) (by omega)
    have hvr : r.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpr
    have h1 : (N / M').factorization p ≥ 1 := (hp.dvd_iff_one_le_factorization hP0).mp hpP
    have h2 : N.factorization p = M'.factorization p + (N / M').factorization p := by
      rw [← Finsupp.add_apply, ← Nat.factorization_mul hM'0' hP0, Nat.mul_div_cancel' hM'N]
    have h3 : N.factorization p = M.factorization p := by
      rw [hN, Nat.factorization_mul hM0 (pow_ne_zero 2 hr0), Nat.factorization_pow]
      simp [hvr]
    have h4 : M.factorization p ≤ M'.factorization p := by
      have := (Nat.factorization_le_iff_dvd hM0 (mul_ne_zero hM'0' (pow_ne_zero 2 hr0))).mpr
        hMdvd p
      rw [Nat.factorization_mul hM'0' (pow_ne_zero 2 hr0), Nat.factorization_pow] at this
      simpa [hvr] using this
    omega
  have hv2 : ∀ p : ℕ, p.Prime → p ∣ r → N.factorization p = 2 := by
    intro p hp hpr
    have hpM : M.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd fun h =>
      hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hpr hcop) h)
    have hr1 : r.factorization p = 1 := by
      have h1 : 1 ≤ r.factorization p := (hp.dvd_iff_one_le_factorization hr0).mp hpr
      have h2 : r.factorization p ≤ 1 := hsq.natFactorization_le_one p
      omega
    rw [hN, Nat.factorization_mul hM0 (pow_ne_zero 2 hr0), Nat.factorization_pow]
    simp [hpM, hr1]
  -- (2) the representation
  have hT : ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
      heckeTCuspNat 2 p (_hn := ⟨hp.ne_zero⟩) (twistJ g r) =
        E.eigenvalue ⟨p, hp.pos⟩ hpN • twistJ g r := fun p hp hpN => by
    have := E.heckeTCuspNat_eq_eigenvalue_smul hp hpN
    rwa [hE] at this
  obtain ⟨c, hc⟩ := exists_coeff_rep hU (twistJ_mem_charSpace g hχ r) hT hM'N g' hg1 hg'ev
  -- (2) the Fricke identity
  obtain ⟨cG, hcG0, hcG⟩ := newform_fricke_ne g hχ
  obtain ⟨cg', -, hcg'⟩ := newform_fricke_ne g' hg1
  set P := N / M' with hP
  have hMP : M' * P = N := Nat.mul_div_cancel' hM'N
  have hP0 : P ≠ 0 := by rintro h0; rw [h0, mul_zero] at hMP; exact hN0 hMP.symm
  set κ := cG * (r : ℂ) ^ 2 * jacobiChar r (-(M : ZMod r)) with hκ
  have hκ0 : κ ≠ 0 := by
    have hχM : jacobiChar r (-(M : ZMod r)) ≠ 0 := by
      intro h0; have := jacobiChar_negM_sq (r := r) hcop'; rw [h0] at this; norm_num at this
    exact mul_ne_zero (mul_ne_zero hcG0 (pow_ne_zero 2 (by exact_mod_cast hr0))) hχM
  have hGcs : g.toCuspForm ∈ cuspFormCharSpace 2 (1 : (ZMod M)ˣ →* ℂˣ) := hχ ▸ g.mem_charSpace
  have hfi : ∀ τ : ℍ, κ * twistJ g r τ = cg' * ∑ e ∈ P.divisors,
      c e * (((P / e : ℕ) : ℂ) ^ 2 * gAt g'.toCuspForm (P / e) τ) := by
    intro τ
    have hM0' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN0
    have hw := im_neg_inv_mul_pos hM0' τ
    have hw' : 0 < (-1 / (((M * r ^ 2 : ℕ) : ℂ) * τ)).im := by
      rw [← hN]; exact_mod_cast hw
    have hw'' : 0 < (-1 / (((M' * P : ℕ) : ℂ) * τ)).im := by
      rw [hMP]; exact_mod_cast hw
    have h1 := twist_fricke hsq hodd hcop' hGcs hcG τ hw'
    have h2 := fricke_sum g' hcg' hP0 c τ hw''
    have hfun := fun_rep_of_coeff_rep (twistJ g r) g' P c hc
    have hpts : (⟨-1 / (((M * r ^ 2 : ℕ) : ℂ) * τ), hw'⟩ : ℍ) =
        ⟨-1 / (((M' * P : ℕ) : ℂ) * τ), hw''⟩ := by
      apply UpperHalfPlane.ext; simp only [UpperHalfPlane.coe_mk]; rw [hMP]
    change twistJ g r _ = _ * twistJ g r τ at h1
    rw [hpts, hfun, hfun τ, h2] at h1
    have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
    apply mul_left_cancel₀ (pow_ne_zero 2 hτ0)
    rw [hfun τ]
    linear_combination -h1
  have hfr := coeff_of_fun_identity (twistJ g r) g' hP0 c hκ0 hfi
  -- (3) the level
  obtain ⟨hbmul, hbpow⟩ := newform_mul_pow g' hg1
  obtain ⟨hgmul, -⟩ := newform_mul_pow g hχ
  have hMeq : M' = N := level_eq_of_reps hN0 hM'N (b := coeff g') (H := H) (c := c)
    g'.isNorm hbmul hbpow
    (fun p hp hpM hpsq => by
      have hex := TauCeti.Nat.IsExactDivisor.of_not_sq_dvd hp hpM hpsq
      have := Newform.qExpansion_coeff_prime_sq_of_isExactDivisor g' hp hex
        (χ₀ := 1) (by rw [hg1, MonoidHom.one_comp])
      rw [MonoidHom.one_apply, Units.val_one, one_mul, sub_self, zpow_zero] at this
      exact this)
    (twistJ_coeff_one g r)
    (fun u v huv => by
      rw [hHf, hHf, hHf, hgmul u v huv]; push_cast; rw [jacobiSym.mul_left]; push_cast; ring)
    (fun p hp hpr j hj => by
      rw [hHf, jacobiSym_prime_pow_eq_zero hp hpr hj]; simp)
    (fun n => hc n) hκ0 hfr hPr hv2
  -- multiplicity one at level `N`
  subst hMeq
  have hmem : twistJ g r ∈ cuspFormCharSpace 2 g'.χ := by
    rw [hg1]; exact twistJ_mem_charSpace g hχ r
  have hfg := g'.eq_qExpansion_coeff_one_smul_of_forall_prime_heckeTCuspNat_eq_smul hmem
    (fun p hp hpN => by rw [hT p hp hpN, ← hg'ev p hp hpN])
  rw [hfg, twistJ_coeff_one, one_smul]
  exact g'.isNew

end ZInQ.GZTheta
