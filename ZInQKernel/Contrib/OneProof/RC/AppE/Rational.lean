import ZInQKernel.Contrib.OneProof.RC.AppE.Galois

/-!
# Appendix E: `a(D)/(a(D₀) z_D)` is rational (the field `rational`)

The 11/5 manuscript, Appendix E, tex 8104–8134: the Galois identity `τ(a(D)) = ν(D/D₀) a(D)` and
the rationality of `a(D)/z_D`, for the algebraic normalized vector, then transported to any form of
the eigenspace with nonzero reference coefficient by the full-space comparison.

`rational_of_ramsey` (PROVED from lane RC8's PRINT `WaldspurgerCor2`, the PRINT
`RamseyAlgebraicModel`, the GLUE hypothesis `HalfIntegralTwist`, entire continuations of the twists,
and `L(E^{(σD₀)}, 1) ≠ 0`).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.AppE

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC.PrintsAnalytic UpperHalfPlane

/-- A number prime to `N` is prime to every `M` whose primes divide `N` (PROVED). -/
theorem coprime_of_support_dvd {N M D : ℕ} (hsupp : ∀ p : ℕ, p.Prime → p ∣ M → p ∣ N)
    (hc : D.Coprime N) : D.Coprime M :=
  Nat.coprime_of_dvd fun p hp hpD hpM =>
    (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.Coprime.coprime_dvd_left hpD hc) (hsupp p hp hpM)

/-- `χ_{−σ}(n)^e = χ_{−σ}(n)` for odd `e` and `n` prime to `N`, `4 ∣ N` (PROVED). -/
theorem kronecker_pow_odd {N : ℕ} (h4 : 4 ∣ N) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {n : ℕ}
    (hn : n.Coprime N) {e : ℕ} (he : Odd e) :
    ((kronecker (-σ) n : ℤ) : ℂ) ^ e = (kronecker (-σ) n : ℂ) := by
  obtain ⟨k, rfl⟩ := he
  rw [pow_succ, pow_mul, kronecker_cpx_sq h4 hσ hn, one_pow, one_mul]

/-- **The Galois comparison** (tex 8086–8134; PROVED from the PRINTs `WaldspurgerCor2` and
`RamseyAlgebraicModel` and the GLUE `HalfIntegralTwist`; the field `rational` of lane RC11's
`EvenPhaseData`). Let `g` lie in the full good-Hecke eigenspace of `E` and `η = ψχ_{−σ}` at a level
`N` (`4 ∣ N`), with `a_g(D₀) ≠ 0`, where `D₀ > 0` is squarefree and prime to `N` and
`L(E^{(σD₀)}, 1) ≠ 0`. For every positive squarefree `D` prime to `N` in the unit squareclasses of
`D₀` at the primes of `N`, `a_g(D)/a_g(D₀) = z_D r` with `r ∈ ℚ` and `z_D = phase N η D₀ D`. -/
theorem rational_of_ramsey (hR : RamseyAlgebraicModel) (hTw : HalfIntegralTwist)
    (hW : WaldspurgerCor2) {E : WeierstrassCurve ℚ} (hE : E.IsElliptic)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist E h) F)
    {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {D₀ : ℕ}
    (hF₀ : ∀ F₀ : ℂ → ℂ, IsLContinuation (qtwist E ((σ * D₀ : ℤ) : ℚ)) F₀ → F₀ 1 ≠ 0)
    {N : ℕ} [NeZero N] (hN : 4 ∣ N) (ψ η : DirichletCharacter ℂ N)
    (hψη : ∀ n : ℕ, n.Coprime N → η n = ψ n * (kronecker (-σ) n : ℂ))
    {g : ℍ → ℂ} (hg : IsInWaldspurgerEigenspace E N ψ η g) (ha₀ : hiwCoeff g D₀ ≠ 0)
    (hD₀ : 0 < D₀) (hsq₀ : Squarefree D₀) (hc₀ : D₀.Coprime N)
    {D : ℕ} (hD : 0 < D) (hsq : Squarefree D) (hc : D.Coprime N)
    (hcl : SameUnitClassesAtLevel N D D₀) :
    ∃ r : ℚ, hiwCoeff g D / hiwCoeff g D₀ = phase N η D₀ D * (r : ℂ) := by
  have hN0 : N ≠ 0 := NeZero.ne N
  obtain ⟨F₀, hF₀c⟩ := hcont _ (ZInQ.Manuscript.RC.Even.sigma_mul_ne_zero hσ hD₀)
  obtain ⟨F, hFc⟩ := hcont _ (ZInQ.Manuscript.RC.Even.sigma_mul_ne_zero hσ hD)
  have hF₀1 := hF₀ F₀ hF₀c
  -- (1) the algebraic normalized vector `g'` (Ramsey)
  obtain ⟨g', hg', halg, h1⟩ := exists_algebraic_normalized hR (NeZero.pos N) hN hg ha₀
  -- (2) `a_g(D)/a_g(D₀) = a_{g'}(D)` (full-space comparison at level `N`)
  have hprop := proportional_of_waldspurgerCor2 hW hE hN ψ η hσ hψη hg hg' hD₀ hD hsq₀ hsq hc₀ hc
    hcl hF₀c hFc hF₀1
  rw [h1, mul_one] at hprop
  have hratio : hiwCoeff g D / hiwCoeff g D₀ = hiwCoeff g' D := by
    rw [hprop, mul_div_assoc, div_self ha₀, mul_one]
  rw [hratio]
  -- (3) the algebraic numbers `A = a_{g'}(D)` and `Z = z_D`
  set w := sqrtRatio N D₀ D with hw
  have hwu : IsUnit w := sqrtRatio_isUnit hN0 hc₀ hc hcl
  set A : Qbar := ⟨hiwCoeff g' D, halg D⟩ with hA
  set Z : Qbar := ⟨η w, dirichlet_mem_Qbar η w⟩ with hZ
  have hZ0 : Z ≠ 0 := by
    intro h0
    apply mulChar_ne_zero_of_isUnit η hwu
    have := congrArg (fun x : Qbar => (x : ℂ)) h0
    simpa [hZ] using this
  have hu₀ : IsUnit (D₀ : ZMod N) := (ZMod.isUnit_iff_coprime D₀ N).mpr hc₀
  have hη₀ : η D₀ ≠ 0 := mulChar_ne_zero_of_isUnit η hu₀
  have hzsq : η w ^ 2 = η D * (η D₀)⁻¹ := phase_sq_eta hN0 η hc₀ hc hcl
  -- (4) every `τ` fixes `A / Z`
  have hfix : ∀ τ : Qbar ≃ₐ[ℚ] Qbar, τ (A / Z) = A / Z := by
    intro τ
    obtain ⟨e, he, hτ⟩ := exists_odd_exponent τ (K := Fintype.card (ZMod N)ˣ) Fintype.card_pos
    have he1 : 1 ≤ e := by obtain ⟨k, rfl⟩ := he; omega
    -- the conjugate `g'^τ`
    obtain ⟨gτ, hgτ, hgτc⟩ := conj_mem_eigenspace hR hN hg' halg τ he hτ
    -- the twist `g' ⊗ ν`
    set ν := η ^ ((e - 1) / 2) with hν
    obtain ⟨M, hNM, hM0, hsupp, f', hf', hf'c⟩ :=
      twist_mem_eigenspace hTw (NeZero.pos N) hN hg' ν
    obtain ⟨hψe, hηe⟩ := twist_chars hN ψ η hσ hψη he
    rw [hψe, hηe] at hf'
    have hgτM := eigen_changeLevel hgτ hNM
    -- the hypotheses of Corollaire 2 at the common level `M`
    have hM4 : 4 ∣ M := dvd_trans hN hNM
    have hψηM : ∀ n : ℕ, n.Coprime M →
        (η ^ e).changeLevel hNM n = (ψ ^ e).changeLevel hNM n * (kronecker (-σ) n : ℂ) := by
      intro n hn
      have hnN : n.Coprime N := Nat.Coprime.coprime_dvd_right hNM hn
      have he0 : e ≠ 0 := by omega
      rw [changeLevel_apply_coprime _ hNM hn, changeLevel_apply_coprime _ hNM hn,
        MulChar.pow_apply' _ he0, MulChar.pow_apply' _ he0, hψη n hnN, mul_pow,
        kronecker_pow_odd hN hσ hnN he]
    have hc₀M := coprime_of_support_dvd hsupp hc₀
    have hcM := coprime_of_support_dvd hsupp hc
    have hclM := sameUnitClasses_of_support hsupp hcl
    have hpropM := proportional_of_waldspurgerCor2 hW hE hM4 _ _ hσ hψηM hgτM hf' hD₀ hD hsq₀
      hsq hc₀M hcM hclM hF₀c hFc hF₀1
    -- read off `τ(A) ν(D₀) = ν(D) A`
    have hτA : hiwCoeff gτ D = ((τ A : Qbar) : ℂ) := hgτc D A rfl
    have hτ1 : hiwCoeff gτ D₀ = 1 := by
      have := hgτc D₀ 1 (by rw [h1]; rfl)
      rw [this, map_one]
      rfl
    rw [hτA, hτ1, hf'c, hf'c, h1, mul_one, mul_one] at hpropM
    -- `ν(D) = z_D^{e−1} ν(D₀)`
    have hu : IsUnit (D : ZMod N) := (ZMod.isUnit_iff_coprime D N).mpr hc
    have hνD : ν D = η D ^ ((e - 1) / 2) := by
      obtain ⟨v, hv⟩ := hu
      rw [← hv, hν, MulChar.pow_apply_coe]
    have hνD₀ : ν D₀ = η D₀ ^ ((e - 1) / 2) := by
      obtain ⟨v, hv⟩ := hu₀
      rw [← hv, hν, MulChar.pow_apply_coe]
    have hνD₀0 : ν D₀ ≠ 0 := by rw [hνD₀]; exact pow_ne_zero _ hη₀
    have hηD : η D = η w ^ 2 * η D₀ := by
      rw [hzsq, mul_assoc, inv_mul_cancel₀ hη₀, mul_one]
    have hνratio : ν D = η w ^ (e - 1) * ν D₀ := by
      rw [hνD, hνD₀, hηD, mul_pow, ← pow_mul]
      congr 2
      obtain ⟨k, rfl⟩ := he
      omega
    rw [hνratio] at hpropM
    have hτA' : ((τ A : Qbar) : ℂ) = η w ^ (e - 1) * (A : ℂ) := by
      apply mul_right_cancel₀ hνD₀0
      rw [hpropM]
      ring
    -- `τ(A) = Z^{e−1} A` and `τ(Z) = Z^e`
    have hτA'' : τ A = Z ^ (e - 1) * A := by
      apply Subtype.ext
      rw [hτA']
      rfl
    have hτZ : τ Z = Z ^ e := by
      apply Subtype.ext
      rw [tau_dirichlet η τ he hτ w Z rfl]
      rfl
    exact ZInQ.Manuscript.RC.Even.galois_fixed_div τ.toRingEquiv.toRingHom hZ0 he1 hτZ hτA''
  -- (5) fixed by every automorphism, hence rational
  obtain ⟨r, hr⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (A / Z)).mpr hfix
  refine ⟨r, ?_⟩
  have hAZ : A = Z * algebraMap ℚ Qbar r := by rw [hr, mul_div_cancel₀ _ hZ0]
  have := congrArg (fun x : Qbar => (x : ℂ)) hAZ
  simp only [hA, hZ, IntermediateField.coe_mul] at this
  rw [this]
  unfold phase
  congr 1

end ZInQ.Manuscript.RC.AppE
