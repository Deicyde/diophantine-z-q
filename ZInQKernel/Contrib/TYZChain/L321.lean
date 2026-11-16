import ZInQKernel.Contrib.TYZChain.Bridge
import ZInQKernel.Contrib.Chebotarev.FrobeniusDenseOfExists

/-!
# TYZ chain, part 2: tyz-321 (`Lemma321Five`, TYZ Lemma 3.21(1), from Shimura reciprocity)

Task tyz-chain (2026-11-14). This module is lines 3214–5477 of `scratch/tyz-321/L321.lean` (task
tyz-321, report `docs/research/tyz-321.md`) unchanged. Lines 1–3213 of that file are identical to
`scratch/cm-bridge/Bridge.lean` lines 1–3213 (checked with `diff`) and are imported here from
`ZInQKernel.Contrib.TYZChain.Bridge` instead of copied. The one other change: the absolute-Frobenius
declarations that tyz-321 copied from `ZInQKernel/Contrib/Chebotarev/FrobeniusDenseOfExists.lean`
(`Zbar`, `toZbar`, `FrobOn`, `FrobExistsFinite`, `FrobExistsAt`, `frobExistsAt_of_finite`,
`frobExistsFinite` and three helper lemmas, about 130 lines) are imported from that module.

Main results: `T321B.betaOneLiftExists` (a lift of `β₁` exists; Dirichlet, Jacobi reciprocity,
absolute Frobenius, compactness of `Gal(ℚ̄/ℚ)`), `T321.lemma321Five_of_shimuraModFn'`
(`Lemma321Five` from `Shimura.ShimuraReciprocityModFn` alone) and
`T321.tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First`.

No `sorry`, no `axiom`.
-/

set_option maxRecDepth 8000


/-! ## §16a. tyz-321: existence of a lift of `β₁` (`BetaOneLiftExists`)

Number theory (`exists_prime_beta`: Dirichlet's theorem for `p ≡ 1 (mod 8)`, `p ≡ −2` modulo the odd parts;
`legendre_eq_betaOneSign`: quadratic reciprocity for Jacobi symbols), the action of an absolute
Frobenius on `√D` (`frob_sqrt`; absolute Frobenius elements copied from
`ZInQKernel/Contrib/Chebotarev/FrobeniusDenseOfExists.lean`), and compactness of `Gal(ℚ̄/ℚ)`
(`betaOneLiftExists`). -/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.T321B

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Package
  NumberField ZMod
open scoped NumberTheorySymbols

/-! ### Number theory: a prime `p` with `(D/p) = betaOneSign D` for finitely many `D` -/

theorem oddPart_facts {D : ℤ} (hD : Squarefree D) :
    oddPartSqfree D % 2 = 1 ∧ (D = oddPartSqfree D ∨ D = 2 * oddPartSqfree D) := by
  unfold oddPartSqfree
  split_ifs with h
  · obtain ⟨c, rfl⟩ := h
    refine ⟨?_, Or.inr (by rw [Int.mul_ediv_cancel_left _ two_ne_zero])⟩
    rw [Int.mul_ediv_cancel_left _ two_ne_zero]
    by_contra hc
    have h4 : (2 : ℤ) * 2 ∣ 2 * c := by
      obtain ⟨e, he⟩ : 2 ∣ c := by omega
      exact ⟨e, by rw [he]; ring⟩
    have := hD 2 h4
    rw [Int.isUnit_iff] at this
    omega
  · exact ⟨by omega, Or.inl rfl⟩

theorem betaOneSign_eq_if {D : ℤ} (hD : Squarefree D) :
    betaOneSign D = if (oddPartSqfree D).natAbs % 8 = 1 ∨ (oddPartSqfree D).natAbs % 8 = 3
      then 1 else -1 := by
  obtain ⟨hodd, hDv⟩ := oddPart_facts hD
  unfold betaOneSign
  set v := oddPartSqfree D with hv
  rcases Int.natAbs_eq v with h | h
  · have hD0 : ¬ D < 0 := by omega
    rw [if_neg hD0, one_mul]
    rw [h] at hodd ⊢
    split_ifs <;> omega
  · have hD0 : D < 0 := by omega
    rw [if_pos hD0]
    rw [h] at hodd ⊢
    split_ifs <;> omega

theorem legendre_eq_betaOneSign (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 1) {D : ℤ}
    (hD : Squarefree D)
    (hpm : (p : ℤ) % ((oddPartSqfree D).natAbs : ℤ) = (-2) % ((oddPartSqfree D).natAbs : ℤ)) :
    legendreSym p D = betaOneSign D := by
  obtain ⟨hodd, hDv⟩ := oddPart_facts hD
  set v := oddPartSqfree D with hv
  set m := v.natAbs with hmdef
  have hm : Odd m := by
    rw [Nat.odd_iff]; omega
  have hpodd : Odd p := Nat.odd_iff.2 (by omega)
  have hp4 : p % 4 = 1 := by omega
  have hJ2 : J(2 | p) = 1 := by
    rw [jacobiSym.at_two hpodd, χ₈_nat_eq_if_mod_eight]
    simp [show p % 2 ≠ 0 by omega, hp8]
  have hJm1 : J(-1 | p) = 1 := by
    rw [jacobiSym.at_neg_one hpodd, χ₄_nat_eq_if_mod_four]
    simp [show p % 2 ≠ 0 by omega, hp4]
  have hJm : J(m | p) = χ₈' m := by
    rw [← jacobiSym.quadratic_reciprocity_one_mod_four hp4 hm, jacobiSym.mod_left' hpm,
      jacobiSym.at_neg_two hm]
  have hJv : J(v | p) = χ₈' m := by
    rcases Int.natAbs_eq v with h | h
    · rw [h, hJm]
    · rw [h, show -((m : ℕ) : ℤ) = -1 * (m : ℤ) by ring, jacobiSym.mul_left, hJm1, one_mul, hJm]
  rw [jacobiSym.legendreSym.to_jacobiSym, betaOneSign_eq_if hD, ← hmdef]
  have hχ : χ₈' (m : ZMod 8) = if m % 8 = 1 ∨ m % 8 = 3 then 1 else -1 := by
    rw [χ₈'_nat_eq_if_mod_eight, if_neg (show ¬ (m % 2 = 0) by rw [Nat.odd_iff] at hm; omega)]
  rcases hDv with h | h
  · rw [h, hJv, hχ]
  · rw [h, jacobiSym.mul_left, hJ2, one_mul, hJv, hχ]

theorem odd_sq_mod_eight {M : ℤ} (hM : M % 2 = 1) : ∃ t : ℤ, M ^ 2 = 8 * t + 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, M = 2 * j + 1 := ⟨M / 2, by omega⟩
  obtain ⟨e, he⟩ := Int.even_mul_succ_self j
  exact ⟨e, by rw [show (2 * j + 1) ^ 2 = 4 * (j * (j + 1)) + 1 by ring, he]; ring⟩

/-- **Dirichlet + CRT**: for finitely many squarefree `D` and any bound `B` there is a prime `p > B`,
`p ≡ 1 (mod 8)`, `p ≡ −2` modulo the odd part of every `D`. -/
theorem exists_prime_beta (S : Finset ℤ) (B : ℕ) :
    ∃ p : ℕ, p.Prime ∧ B < p ∧ p % 8 = 1 ∧ ∀ D ∈ S, Squarefree D →
      (p : ℤ) % ((oddPartSqfree D).natAbs : ℤ) = (-2) % ((oddPartSqfree D).natAbs : ℤ) := by
  classical
  set f : ℤ → ℕ := fun D => if Squarefree D then (oddPartSqfree D).natAbs else 1 with hf
  set M : ℕ := ∏ D ∈ S, f D with hM
  have hfodd : ∀ D, Odd (f D) := by
    intro D
    simp only [hf]
    split_ifs with h
    · rw [Nat.odd_iff]; have := (oddPart_facts h).1; omega
    · exact odd_one
  have hModd : Odd M := Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one
    (fun D _ => hfodd D)
  have hM2 : (M : ℤ) % 2 = 1 := by rw [Nat.odd_iff] at hModd; omega
  obtain ⟨t, ht⟩ := odd_sq_mod_eight hM2
  set a : ℤ := 3 * (M : ℤ) ^ 2 - 2 with ha
  have hcop : IsCoprime a ((8 * M : ℕ) : ℤ) := by
    push_cast
    refine IsCoprime.mul_right ?_ ?_
    · rw [show (8 : ℤ) = 2 ^ 3 by norm_num]
      refine IsCoprime.pow_right ?_
      exact ⟨1, -(12 * t), by rw [ha, ht]; ring⟩
    · obtain ⟨j, hj⟩ : ∃ j, (M : ℤ) = 2 * j + 1 := ⟨(M : ℤ) / 2, by omega⟩
      exact ⟨j, 1 - 3 * j * M, by rw [ha, hj]; ring⟩
  obtain ⟨p, hpB, hp, hpa⟩ := Nat.forall_exists_prime_gt_and_zmodEq B
    (q := 8 * M) (by have := hModd.pos; omega) hcop
  refine ⟨p, hp, hpB, ?_, ?_⟩
  · have h8 : (p : ℤ) ≡ a [ZMOD 8] := Int.ModEq.of_mul_right M (by push_cast at hpa; exact hpa)
    have : a % 8 = 1 := by rw [ha, ht]; omega
    have := h8.eq
    omega
  · intro D hD hsq
    have hdvd : ((oddPartSqfree D).natAbs : ℤ) ∣ (M : ℤ) := by
      have : f D ∣ M := Finset.dvd_prod_of_mem f hD
      simp only [hf, if_pos hsq] at this
      exact_mod_cast this
    have h1 : (p : ℤ) ≡ a [ZMOD ((oddPartSqfree D).natAbs : ℤ)] :=
      Int.ModEq.of_dvd (by rw [Nat.cast_mul, Nat.cast_ofNat]; exact Dvd.dvd.mul_left hdvd 8) hpa
    have h2 : a ≡ -2 [ZMOD ((oddPartSqfree D).natAbs : ℤ)] := by
      rw [Int.modEq_iff_dvd, ha, show (-2 : ℤ) - (3 * (M : ℤ) ^ 2 - 2) = (M : ℤ) * (-3 * M) by ring]
      exact Dvd.dvd.mul_right hdvd _
    exact (h1.trans h2)

/-! ### Absolute Frobenius elements

tyz-321 copied these from `ZInQKernel/Contrib/Chebotarev/FrobeniusDenseOfExists.lean` (namespace
`ZInQ.Contrib.ChebFD.C10`, `GQ` renamed `GalQ`; both are the abbreviation
`AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ`). tyz-chain imports them instead. -/

open ZInQ.Contrib.ChebFD.C10 (Zbar toZbar toZbar_coe FrobOn FrobExistsFinite FrobExistsAt
  frobExistsAt_of_finite frobExistsFinite)

theorem natCast_mem (P : Ideal Zbar) (p : ℕ) (hPp : P.under ℤ = Ideal.span {(p : ℤ)}) :
    (p : Zbar) ∈ P := by
  have h1 : (p : ℤ) ∈ P.under ℤ := by rw [hPp]; exact Ideal.mem_span_singleton_self _
  have h2 : algebraMap ℤ Zbar (p : ℤ) ∈ P := h1
  simpa using h2

/-! ### The Frobenius at `p` acts on `√D` by `(D/p)` -/

theorem isIntegral_sqrt {D : ℤ} {r : Qbar} (hr : r ^ 2 = (D : Qbar)) : IsIntegral ℤ r := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C D, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub_C _ two_ne_zero
  · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, hr]; simp

theorem frob_sqrt (p : ℕ) [hpf : Fact p.Prime] (hp2 : p ≠ 2) (h : GalQ) (P : Ideal Zbar) [P.IsPrime]
    (hPp : P.under ℤ = Ideal.span {(p : ℤ)})
    (hh : ∀ x y : Zbar, (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P)
    {D : ℤ} (hpD : ¬ (p : ℤ) ∣ D) {r : Qbar} (hr : r ^ 2 = (D : Qbar)) :
    h r = (legendreSym p D : Qbar) * r := by
  set L := legendreSym p D with hL
  have hL2 : L = 1 ∨ L = -1 := by
    have hD0 : (D : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hpD
    rcases legendreSym.eq_one_or_neg_one p hD0 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have hhr2 : (h r) ^ 2 = (D : Qbar) := by rw [← map_pow, hr, map_intCast]
  have hc2 : ((2 : Zbar) : Qbar) = 2 := rfl
  have hc4 : ((4 : Zbar) : Qbar) = 4 := rfl
  have hri := isIntegral_sqrt hr
  have hhri := isIntegral_sqrt hhr2
  set xr : Zbar := ⟨r, hri⟩
  set xh : Zbar := ⟨h r, hhri⟩
  -- `h r − r^p ∈ P`
  have h1 : xh - xr ^ p ∈ P := hh xr (xh - xr ^ p) (by simp [xr, xh])
  -- `r^p − L r = r (D^{p/2} − L) ∈ P`
  have hpodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two (Fact.out)).2 hp2
  have hrp : xr ^ p = xr * (D : Zbar) ^ (p / 2) := by
    apply Subtype.ext
    simp only [SubmonoidClass.coe_pow, MulMemClass.coe_mul, xr]
    have e : p = 2 * (p / 2) + 1 := by omega
    have hcD : (((D : Zbar)) : Qbar) = (D : Qbar) := by simp
    rw [hcD]
    calc r ^ p = r ^ (2 * (p / 2) + 1) := by rw [← e]
      _ = (r ^ 2) ^ (p / 2) * r := by ring
      _ = r * (D : Qbar) ^ (p / 2) := by rw [hr]; ring
  have hdvd : (p : ℤ) ∣ D ^ (p / 2) - L := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hL, legendreSym.eq_pow]; ring
  obtain ⟨c, hc⟩ := hdvd
  have h2 : xr ^ p - (L : Zbar) * xr ∈ P := by
    rw [hrp]
    have : xr * (D : Zbar) ^ (p / 2) - (L : Zbar) * xr = xr * ((p : Zbar) * (c : Zbar)) := by
      have hc' : ((D ^ (p / 2) - L : ℤ) : Zbar) = (((p : ℤ) * c : ℤ) : Zbar) := by rw [hc]
      push_cast at hc'
      linear_combination xr * hc'
    rw [this]
    exact P.mul_mem_left _ (P.mul_mem_right _ (natCast_mem P p hPp))
  have h3 : xh - (L : Zbar) * xr ∈ P := by
    have := P.add_mem h1 h2
    rwa [show xh - xr ^ p + (xr ^ p - (L : Zbar) * xr) = xh - (L : Zbar) * xr by ring] at this
  -- `h r = ± r`
  have hpm : h r = r ∨ h r = -r := sq_eq_sq_iff_eq_or_eq_neg.1 (hhr2.trans hr.symm)
  by_contra hne
  have hneg : h r = -((L : Qbar) * r) := by
    rcases hL2 with hl | hl <;> rcases hpm with hp' | hp'
    · exact absurd (by rw [hp', hl]; push_cast; ring) hne
    · rw [hp', hl]; push_cast; ring
    · rw [hp', hl]; push_cast; ring
    · exact absurd (by rw [hp', hl]; push_cast; ring) hne
  have h4 : (2 * (L : Zbar)) * xr ∈ P := by
    have : xh - (L : Zbar) * xr = -((2 * (L : Zbar)) * xr) := by
      apply Subtype.ext
      simp only [xh, xr, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, NegMemClass.coe_neg]
      rw [hneg]; push_cast; rw [hc2]; ring
    rw [this] at h3
    exact (neg_mem_iff).1 h3
  have h5 : ((4 * D : ℤ) : Zbar) ∈ P := by
    have := P.mul_mem_left ((2 * (L : Zbar)) * xr) h4
    have e : (2 * (L : Zbar)) * xr * ((2 * (L : Zbar)) * xr) = ((4 * D : ℤ) : Zbar) := by
      apply Subtype.ext
      simp only [xr, MulMemClass.coe_mul]
      push_cast
      have hl2 : (L : Qbar) ^ 2 = 1 := by rcases hL2 with hl | hl <;> simp [hl]
      rw [hc2, hc4]
      linear_combination (4 * (L : Qbar) ^ 2) * hr + 4 * (D : Qbar) * hl2
    rwa [e] at this
  have h6 : (4 * D : ℤ) ∈ P.under ℤ := by
    show algebraMap ℤ Zbar (4 * D) ∈ P
    simpa using h5
  rw [hPp, Ideal.mem_span_singleton] at h6
  have hp := hpf.out
  have : (p : ℤ) ∣ 4 ∨ (p : ℤ) ∣ D := (Int.prime_iff_natAbs_prime.2 (by simpa using hp)).dvd_or_dvd h6
  rcases this with h7 | h7
  · have h8 : p ∣ 2 ^ 2 := by exact_mod_cast h7
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h8))
  · exact hpD h7

/-! ### Finite level and compactness -/

theorem exists_finite_beta (S : Finset ℤ) : ∃ σ : GalQ, ∀ D ∈ S, Squarefree D →
    ∀ r : Qbar, r ^ 2 = (D : Qbar) → σ r = (betaOneSign D : Qbar) * r := by
  obtain ⟨p, hp, hpB, hp8, hcong⟩ := exists_prime_beta S (∑ D ∈ S, D.natAbs)
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  haveI : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  obtain ⟨P, -, hP, hPp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {(p : ℤ)})
    (⊥ : Ideal Zbar) (by
      intro x hx
      rw [Ideal.mem_comap, Ideal.mem_bot] at hx
      have hx' : ((algebraMap ℤ Zbar x : Zbar) : Qbar) = 0 := by rw [hx]; rfl
      have : (x : Qbar) = 0 := by simpa using hx'
      have hx0 : x = 0 := by exact_mod_cast this
      rw [hx0]; exact Ideal.zero_mem _)
  obtain ⟨h, hh⟩ := frobExistsAt_of_finite frobExistsFinite p P hPp
  refine ⟨h, fun D hD hsq r hr => ?_⟩
  have hD0 : D ≠ 0 := hsq.ne_zero
  have hpD : ¬ (p : ℤ) ∣ D := by
    intro hdvd
    have h1 : D.natAbs ≤ ∑ D ∈ S, D.natAbs :=
      Finset.single_le_sum (f := fun D : ℤ => D.natAbs) (fun _ _ => Nat.zero_le _) hD
    have h2 : p ∣ D.natAbs := by
      have := Int.natAbs_dvd_natAbs.2 hdvd
      simpa using this
    have h3 := Nat.le_of_dvd (Int.natAbs_pos.2 hD0) h2
    omega
  rw [frob_sqrt p hp2 h P hPp hh hpD hr, legendre_eq_betaOneSign p hp8 hsq (hcong D hD hsq)]

/-- **Glue BETA-EX proved**: a lift of `β₁ = r_∞(−1)r₂(−2)` exists (compactness of `Gal(ℚ̄/ℚ)`;
at each finite level a Frobenius at a prime `p ≡ 1 (mod 8)`, `p ≡ −2` modulo the odd parts, by
Dirichlet, acts on `√D` by `(D/p) = betaOneSign D`, by quadratic reciprocity). -/
theorem betaOneLiftExists : ∃ σ : GalQ, IsBetaOneLift σ := by
  let t : Finset ℤ → Set GalQ := fun S => {σ | ∀ D ∈ S, Squarefree D →
    ∀ r : Qbar, r ^ 2 = (D : Qbar) → σ r = (betaOneSign D : Qbar) * r}
  have htd : Directed (· ⊇ ·) t := by
    intro S S'
    refine ⟨S ∪ S', fun σ hσ D hD => hσ D (Finset.mem_union_left _ hD),
      fun σ hσ D hD => hσ D (Finset.mem_union_right _ hD)⟩
  have htn : ∀ S, (t S).Nonempty := fun S => exists_finite_beta S
  have htcl : ∀ S, IsClosed (t S) := by
    intro S
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro σ hσ
    simp only [t, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hσ
    obtain ⟨D, hD, hsq, r, hr, hne⟩ := hσ
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {r}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral r)
    refine ⟨(fun k => σ⁻¹ * k) ⁻¹' ((IntermediateField.adjoin ℚ {r}).fixingSubgroup : Set GalQ),
      ?_, ?_, ?_⟩
    · intro k hk hkt
      have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hk r
        (IntermediateField.mem_adjoin_simple_self ℚ r)
      change σ⁻¹ (k r) = r at hfix
      have hkr : k r = σ r := by
        have e := congrArg σ hfix
        rwa [show σ (σ⁻¹ (k r)) = k r from AlgEquiv.apply_symm_apply σ _] at e
      exact hne (hkr ▸ hkt D hD hsq r hr)
    · exact (IntermediateField.fixingSubgroup_isOpen _).preimage
        (continuous_const.mul continuous_id)
    · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
      exact one_mem _
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn
    (fun S => (htcl S).isCompact) htcl
  refine ⟨σ, fun D hsq r hr => ?_⟩
  exact (Set.mem_iInter.1 hσ {D}) D (Finset.mem_singleton_self D) hsq r hr

end ZInQ.Contrib.TYZGenus.T321B

/-! ## §16. tyz-321: `Lemma321Five` (TYZ Lemma 3.21(1)) from Shimura reciprocity, ring class field
theory and genus theory

Task tyz-321 (2026-11-14). Report: `docs/research/tyz-321.md`; log: `scratch/tyz-321/log.md`.
Everything above this section is a verbatim copy of `scratch/cm-bridge/Bridge.lean` (§0–§15, without
its axiom-audit lines), which contains the statement `CMBridge.Lemma321Five` and everything it
depends on. -/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.T321

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.Package
  ZInQ.Contrib.TYZGenus.RingClass ZInQ.Contrib.TYZGenus.CMBridge ZInQ.PropN NumberField
  TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields TauCeti.GlobalNumberFields.NumberFieldOrder
  ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZGenus.RingClassBridge

/-! ### The class of `σ_ϖ` -/

/-- The odd part `𝔞 = (m, √−d − 1)`, `m = (d+1)/2`, of the principal ideal `(√−d − 1)` of
`𝓞_{K_d} = ℤ[√−d]` (`d ≡ 1 (mod 4)`): `(√−d − 1) = 𝔭₂ 𝔞`, `N𝔞 = m` (odd for `d ≡ 5 (mod 8)`). -/
def varpiIdeal (d : ℕ) [NeZero d] : Ideal (𝓞 (QNeg d)) :=
  Ideal.span {(((d + 1) / 2 : ℕ) : 𝓞 (QNeg d)), sqrtNeg d - 1}

open Classical in
/-- **The class `w ∈ Pic(O_{d,4})` of TYZ's `σ_ϖ`, `ϖ = √−d − 1`**: the Picard class of the contraction
of `𝔞` (`varpiIdeal`), an ideal prime to the conductor (`1` otherwise; never taken for
`d ≡ 5 (mod 8)`). The idele `ϖ` at the place 2 and the ideal `(ϖ)𝔭₂⁻¹ = 𝔞` have inverse Artin
symbols, so `w = σ_ϖ^{∓1}`; TYZ's `ϖ = 1 + √−d` gives the conjugate ideal, i.e. `w^{−1}`. The
statements below only use `w` modulo `ℤτ(1)` and are insensitive to `w ↔ w⁻¹`. -/
def wClass (d : ℕ) [NeZero d] : Pic (O4 d) :=
  if h : varpiIdeal d ∈ integralIdealsPrimeTo (O4 d).conductorModulus then (O4 d).picClass ⟨_, h⟩
  else 1

/-! ### The inputs (named `Prop`s) -/

/-- **Glue BETA-EX (existence of a lift of `β₁`)**: some `σ ∈ Gal(ℚ̄/ℚ)` acts on every quadratic field
as the idele `β₁ = r_∞(−1)r₂(−2)`. True because `D ↦ betaOneSign D` is a character of
`ℚ^×/ℚ^{×2}` (product of Hilbert symbols) and `Gal(ℚ(√D : D)/ℚ) = Hom(ℚ^×/ℚ^{×2}, ±1)` (Kummer
theory, with compactness of `Gal(ℚ̄/ℚ)`). TYZ L2496–2500 take "any lifting" of `β₁`. -/
def BetaOneLiftExists : Prop := ∃ σ : GalQ, IsBetaOneLift σ

/-- `z_n ∈ A(H_{n,4})` (consequence of the CM field of definition; proved below from
`Shimura.ShimuraReciprocityModFn`). -/
def ZnOverH4 : Prop := ∀ n : ℕ, n % 8 = 5 → Squarefree n → tyzZn n ∈ ptsOver (H4bar n)

/-- **TYZ Theorem 3.6(1), conjugation part (pinned)**: `z̄_n = −z_n + τ(1)` for squarefree
`n ≡ 5 (mod 8)` and complex conjugation `γ` (TYZ L1408–1428, as re-derived in rv-tyz-inputs §1.5,
"`z̄_n = −z_n + τ(1)`"). `τ(1) = tauG 2 = (0,0)`. -/
def TYZThm36ConjFive : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → ∀ γ : GalQ, IsComplexConj γ →
    galPt γ (tyzZn n) = tauG 2 - tyzZn n

/-- **TYZ Theorem 3.6(1), `σ_ϖ` part (pinned, modulo `ℤτ(1)`)**: every `ρ` acting on `H_{n,4}` as
the Artin symbol of `w = [𝔞]` moves `z_n` by `τ((1+i)/2) = tauG (1+i)` modulo `ℤτ(1)`. TYZ
Theorem 3.6(1): `z_n^{σ_ϖ} = z_n + τ((1+i)/2)` (rv-tyz-inputs §1.5). -/
def TYZThm36OneFive : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 5 → Squarefree n → ∀ ρ : GalQ, ActsAsArtin4 ρ n (wClass n) →
    ∃ k : ℤ, galPt ρ (tyzZn n) = tyzZn n + tauG ⟨1, 1⟩ + k • tauG 2

/-- **Glue W-I (`σ_w` negates `i`)**: every `ρ` acting on `H_{n,4}` as `w` maps `i` to `−i`. Genus
theory: `K_n(i) = K_n(√n) ⊆ H_n` and `Art(𝔞)` acts on it by `Π_{q ∣ n} χ_q([𝔞]) = Π_q (N𝔞/q) =
Π_q (2/q) = (2/n) = −1` (`N𝔞 = (n+1)/2 ≡ 1/2 mod q`, `n ≡ 5 (mod 8)`). -/
def WNegatesI : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 5 → Squarefree n → ∀ ρ : GalQ, ActsAsArtin4 ρ n (wClass n) →
    ρ iQ = -iQ

/-- **Glue KER (`Gal(H_{n,4}/H_n)` moves `z_n` only by `ℤτ(1)`)**: TYZ L2540 ("`z_n^σ ∈ z_n + {0, τ(1)}`"
for `σ ∈ Gal(H'_n/H_n)`). -/
def KerFixesZnMod : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 5 → Squarefree n → ∀ k : Pic (O4 n), picToMax (O4 n) k = 1 →
    ∀ ρ : GalQ, ActsAsArtin4 ρ n k → ∃ j : ℤ, galPt ρ (tyzZn n) = tyzZn n + j • tauG 2

/-- **Glue BETA-5 (`β₁` on the genus field, class 5)**: for a lift `σ` of `β₁` and complex conjugation
`γ`, the class `a ∈ Pic(O_{n,4})` of `σγ⁻¹` (which fixes `K_n`) is `w` modulo squares in `Cl(K_n)`.
TYZ L2526–2531 ("`β'_j` acts on `L_n(i)` as `σ_ϖ ∘ c`"); by genus theory (`Cl² = ⋂ ker χ_q`) it is
the equality of genus characters `χ_q(a) = χ_q(w) = (2/q)` for `q ∣ n`. -/
def BetaOnGenus5 : Prop :=
  ∀ n : ℕ, ∀ _ : NeZero n, n % 8 = 5 → Squarefree n → ∀ σ γ : GalQ, IsBetaOneLift σ →
    IsComplexConj γ → ∀ a : Pic (O4 n), ActsAsArtin4 (σ * γ⁻¹) n a →
      picToMax (O4 n) (a * (wClass n)⁻¹) ∈ picSquares (OK n)

/-! ### Glue: Artin symbols of `O_{d,4}` in `ℚ̄` -/

section Acts4

variable {d : ℕ} [NeZero d]

theorem acts4_iff {ρ : GalQ} {c : Pic (O4 d)} : ActsAsArtin4 ρ d c ↔ ActsAsArtinO d (O4 d) ρ c :=
  Iff.rfl

theorem acts4_mul {ρ ρ' : GalQ} {c c' : Pic (O4 d)} (hρ : ActsAsArtin4 ρ d c)
    (hρ' : ActsAsArtin4 ρ' d c') : ActsAsArtin4 (ρ * ρ') d (c * c') := by
  intro x
  rw [AlgEquiv.mul_apply, hρ' x, hρ (artin4 d c' x), map_mul, AlgEquiv.mul_apply]

theorem acts4_agree {ρ ρ' : GalQ} {c : Pic (O4 d)} (hρ : ActsAsArtin4 ρ d c)
    (hρ' : ActsAsArtin4 ρ' d c) : ∀ x ∈ H4bar d, ρ x = ρ' x := by
  intro x hx
  rw [H4bar_eq] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have h1 : ρ (embed d y) = embed d ((artin4 d c ⟨y, hy⟩ : H4 d) : SeparableClosure (QNeg d)) :=
    hρ ⟨y, hy⟩
  have h2 : ρ' (embed d y) = embed d ((artin4 d c ⟨y, hy⟩ : H4 d) : SeparableClosure (QNeg d)) :=
    hρ' ⟨y, hy⟩
  change ρ (embed d y) = ρ' (embed d y)
  rw [h1, h2]

theorem acts4_galPt {ρ ρ' : GalQ} {c : Pic (O4 d)} (hρ : ActsAsArtin4 ρ d c)
    (hρ' : ActsAsArtin4 ρ' d c) {P : PtA} (hP : P ∈ ptsOver (H4bar d)) :
    galPt ρ P = galPt ρ' P :=
  galPt_congr (acts4_agree hρ hρ') hP

/-- The image of `√−d` in `ℚ̄`. -/
abbrev omegaBar (d : ℕ) [NeZero d] : Qbar :=
  embed d (algebraMap (QNeg d) (SeparableClosure (QNeg d)) QuadraticAlgebra.omega)

theorem omegaBar_sq : omegaBar d ^ 2 = -(d : Qbar) := by
  simp only [omegaBar]
  rw [← map_pow, ← map_pow]
  simp [QuadraticAlgebra.omega_pow_two_eq_add]

/-- **An automorphism of `ℚ̄` fixing `K_d` acts on `H_{d,4}` as an Artin symbol.** -/
theorem exists_acts4_of_fix {ρ : GalQ} (hρ : ρ (omegaBar d) = omegaBar d) :
    ∃ a : Pic (O4 d), ActsAsArtin4 ρ d a := by
  have hb := (Algebra.IsAlgebraic.algHom_bijective₂ (embed d)
    (IsAlgClosed.lift : Qbar →ₐ[ℚ] SeparableClosure (QNeg d))).1
  set e := AlgEquiv.ofBijective (embed d) hb
  set τ : SeparableClosure (QNeg d) ≃ₐ[ℚ] SeparableClosure (QNeg d) := e.trans (ρ.trans e.symm)
  have he : ∀ y, e y = embed d y := fun y => rfl
  have hγτ : ∀ y, ρ (embed d y) = embed d (τ y) := by
    intro y
    rw [← he, ← he]
    simp [τ]
  have hτω : τ (algebraMap (QNeg d) _ QuadraticAlgebra.omega) =
      algebraMap (QNeg d) _ QuadraticAlgebra.omega := by
    apply (embed d).injective
    change embed d (τ _) = embed d _
    rw [← hγτ]
    exact hρ
  have hq : ∀ q : ℚ, τ (algebraMap (QNeg d) (SeparableClosure (QNeg d)) (algebraMap ℚ (QNeg d) q)) =
      algebraMap (QNeg d) (SeparableClosure (QNeg d)) (algebraMap ℚ (QNeg d) q) := by
    intro q
    rw [← IsScalarTower.algebraMap_apply]
    exact τ.commutes q
  have hcomm : ∀ k : QNeg d, τ (algebraMap (QNeg d) (SeparableClosure (QNeg d)) k) =
      algebraMap (QNeg d) (SeparableClosure (QNeg d)) k := by
    intro k
    have hk : k = algebraMap ℚ (QNeg d) k.re + algebraMap ℚ (QNeg d) k.im * QuadraticAlgebra.omega := by
      ext <;> simp
    rw [hk, map_add, map_mul, map_add, map_mul, hq, hq, hτω]
  let τK : SeparableClosure (QNeg d) ≃ₐ[QNeg d] SeparableClosure (QNeg d) :=
    { τ with commutes' := hcomm }
  refine ⟨(artin4 d).symm (AlgEquiv.restrictNormal τK (H4 d)), fun x => ?_⟩
  rw [MulEquiv.apply_symm_apply, hγτ]
  congr 1
  exact (AlgEquiv.restrictNormal_commutes τK (H4 d) x).symm

end Acts4

/-! ### Glue: torsion bookkeeping -/

section Tors

theorem galPt_tauG_two (ρ : GalQ) : galPt ρ (tauG 2) = tauG 2 := by
  rw [← one_add_one_eq_two, map_add, tauG_apply, one_smul, map_add, galPt_ptT]

theorem tauG_one_one_add : tauG ⟨1, 1⟩ + tauG ⟨1, -1⟩ = tauG 2 := by
  rw [← map_add]; rfl

theorem iQ_cases (ρ : GalQ) : ρ iQ = iQ ∨ ρ iQ = -iQ := by
  have h : (ρ iQ) ^ 2 = iQ ^ 2 := by rw [← map_pow, iQ_sq, map_neg, map_one]
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h

/-- An automorphism negating `i` anticommutes with `[i]`. -/
theorem galPt_iPt_of_neg {ρ : GalQ} (hρ : ρ iQ = -iQ) (P : PtA) :
    galPt ρ (iPt P) = -iPt (galPt ρ P) := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h1, e1⟩ := galPt_some ρ (nonsingular_iPt h)
    obtain ⟨h2, e2⟩ := galPt_some ρ h
    rw [iPt_some, e1, e2, iPt_some, WeierstrassCurve.Affine.Point.neg_some,
      WeierstrassCurve.Affine.Point.some.injEq]
    refine ⟨by rw [map_neg], ?_⟩
    rw [map_mul, hρ]
    simp only [WeierstrassCurve.Affine.negY, curveAbar_a₁, curveAbar_a₃]
    ring

theorem galPt_tauG_one_one (ρ : GalQ) :
    ∃ j : ℤ, galPt ρ (tauG ⟨1, 1⟩) = tauG ⟨1, 1⟩ + j • tauG 2 := by
  rcases iQ_cases ρ with h | h
  · exact ⟨0, by rw [galPt_tauG ρ h, zero_zsmul, add_zero]⟩
  · refine ⟨1, ?_⟩
    have h2 : tauG 2 = (2 : ℤ) • iPt ptT := by
      rw [two_zsmul_iPt_ptT, ← two_zsmul_ptT, ← one_add_one_eq_two, map_add, tauG_apply, one_smul,
        two_zsmul]
    have h4 : (4 : ℤ) • iPt ptT = 0 := by
      rw [show (4 : ℤ) = 2 + 2 by norm_num, add_zsmul, two_zsmul_iPt_ptT, pt00_add_self]
    rw [tauG_mk, map_add, one_smul, one_smul, galPt_ptT, galPt_iPt_of_neg h, galPt_ptT, one_smul,
      h2]
    have : -iPt ptT = iPt ptT + (2 : ℤ) • iPt ptT - (4 : ℤ) • iPt ptT := by
      rw [show (4 : ℤ) = 1 + 2 + 1 by norm_num, add_zsmul, add_zsmul, one_zsmul]; abel
    rw [this, h4]; abel

end Tors

/-! ### `TYZThm36ConjFive` from the Fricke involution and `τ ↦ τ + 1/4`

`τ_{Q̄} = W T₄ W τ_Q` (`W τ = −1/(32τ)`, `T₄ τ = τ + 1/4`), `φ(Wτ) = T − φ(τ)` (Fricke, proved by
tyz-cm) and `φ(τ + 1/4) = [i]φ(τ)` (proved here from the theta form of `x` and the eta form of `y`),
so `c(f₀(P_n)) = f₀(P_{Q̄}) = [i]f₀(P_n) + T − [i]T` and `c(z_n) = −z_n + τ(1)`. -/

section Conj

open Complex WeierstrassCurve.Affine

theorem etaD_add_quarter {d m : ℕ} (h : d = 4 * m) (z : ℂ) :
    X0.etaD d (z + 1 / 4) = cexp (2 * Real.pi * I / 24) ^ m * X0.etaD d z := by
  unfold X0.etaD
  rw [show (d : ℂ) * (z + 1 / 4) = d * z + (m : ℕ) by rw [h]; push_cast; ring, X0.eta_add_nat,
    ← Complex.exp_nat_mul]
  congr 2
  ring

theorem cexp_pi_div_two : cexp (Real.pi / 2 * I) = I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_ofNat, ← Complex.ofReal_div, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

theorem cexp_pow_6 : cexp (2 * Real.pi * I / 24) ^ 6 = I := by
  rw [← Complex.exp_nat_mul,
    show ((6 : ℕ) : ℂ) * (2 * Real.pi * I / 24) = Real.pi / 2 * I by push_cast; ring]
  exact cexp_pi_div_two

/-- **`y(z + 1/4) = i·y(z)`** (`y` is an eta quotient in `η(4z), η(8z), η(16z), η(32z)`). -/
theorem yC_add_quarter (z : ℂ) : X0.yC (z + 1 / 4) = I * X0.yC z := by
  unfold X0.yC
  rw [etaD_add_quarter (m := 2) (by norm_num), etaD_add_quarter (m := 4) (by norm_num),
    etaD_add_quarter (m := 1) (by norm_num), etaD_add_quarter (m := 8) (by norm_num)]
  set c := cexp (2 * Real.pi * I / 24)
  have hc : c ≠ 0 := Complex.exp_ne_zero _
  have key : c ^ 16 = I * c ^ 34 := by
    rw [← cexp_pow_6, show c ^ 34 = c ^ 10 * c ^ 24 by ring, X0.cexp_pow_24]; ring
  have e : (c ^ 2 * X0.etaD 8 z) ^ 4 * (c ^ 4 * X0.etaD 16 z) ^ 2 /
      ((c ^ 1 * X0.etaD 4 z) ^ 2 * (c ^ 8 * X0.etaD 32 z) ^ 4) =
      c ^ 16 * (X0.etaD 8 z ^ 4 * X0.etaD 16 z ^ 2) /
        (c ^ 34 * (X0.etaD 4 z ^ 2 * X0.etaD 32 z ^ 4)) := by ring
  rw [e, key, show I * c ^ 34 * (X0.etaD 8 z ^ 4 * X0.etaD 16 z ^ 2) =
    c ^ 34 * (I * (X0.etaD 8 z ^ 4 * X0.etaD 16 z ^ 2)) by ring,
    mul_div_mul_left _ _ (pow_ne_zero _ hc)]
  ring

/-- `τ ↦ τ + 1/4` on `ℍ`. -/
def quarterH (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(τ : ℂ) + 1 / 4, by
    show 0 < ((τ : ℂ) + 1 / 4).im
    simpa using τ.im_pos⟩

theorem Qt_add_quarter (z : ℂ) : Shimura.Qt (z + 1 / 4) = Shimura.Qt z * I := by
  rw [Shimura.Qt_def, Shimura.Qt_def,
    show 2 * Real.pi * I * (z + 1 / 4) = 2 * Real.pi * I * z + Real.pi / 2 * I by ring,
    Complex.exp_add, cexp_pi_div_two]

/-- **`x(τ + 1/4) = −x(τ)`** (`x = 2θ(0;16τ)/(q²θ(8τ;16τ))`, tyz-cm's `xC_theta`). -/
theorem xC_add_quarter (τ : UpperHalfPlane) : X0.xC ((τ : ℂ) + 1 / 4) = -X0.xC τ := by
  have h1 := Shimura.xC_theta (quarterH τ)
  have h2 := Shimura.xC_theta τ
  change X0.xC ((quarterH τ : UpperHalfPlane) : ℂ) = _
  rw [h1, h2]
  have e1 : (16 : ℂ) * ((quarterH τ : UpperHalfPlane) : ℂ) = 16 * τ + 2 + 2 := by
    show (16 : ℂ) * ((τ : ℂ) + 1 / 4) = _; ring
  have e2 : (8 : ℂ) * ((quarterH τ : UpperHalfPlane) : ℂ) = 8 * τ + 1 + 1 := by
    show (8 : ℂ) * ((τ : ℂ) + 1 / 4) = _; ring
  have e3 : Shimura.Qt ((quarterH τ : UpperHalfPlane) : ℂ) = Shimura.Qt τ * I :=
    Qt_add_quarter τ
  rw [e1, e2, e3]
  simp only [jacobiTheta₂_add_right, jacobiTheta₂_add_left]
  rw [mul_pow, I_sq]
  ring

theorem curveAC_a₂ : X0.curveAC.a₂ = 0 := by
  simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
theorem curveAC_a₄ : X0.curveAC.a₄ = 4 := by
  simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]
theorem curveAC_a₆ : X0.curveAC.a₆ = 0 := by
  simp [X0.curveAC, curveA, shortCurve, WeierstrassCurve.baseChange]

theorem nonsingular_iC {x y : ℂ} (h : X0.curveAC.toAffine.Nonsingular x y) :
    X0.curveAC.toAffine.Nonsingular (-x) (I * y) := by
  rw [nonsingular_iff', equation_iff'] at h ⊢
  simp only [Shimura.curveAC_a₁, curveAC_a₂, Shimura.curveAC_a₃, curveAC_a₄, curveAC_a₆] at h ⊢
  obtain ⟨he, hn⟩ := h
  refine ⟨by linear_combination y ^ 2 * I_sq - he, ?_⟩
  rcases hn with h | h
  · left
    intro h'
    apply h
    linear_combination h'
  · right
    intro h'
    apply h
    have : I * (2 * y) = 0 := by linear_combination h'
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 I_ne_zero
    · linear_combination h0

theorem nonsingular_iC_iff {x y : ℂ} :
    X0.curveAC.toAffine.Nonsingular (-x) (I * y) ↔ X0.curveAC.toAffine.Nonsingular x y := by
  refine ⟨fun h => ?_, nonsingular_iC⟩
  have h2 := nonsingular_iC h
  have e1 : -(-x) = x := neg_neg x
  have e2 : I * (I * y) = X0.curveAC.toAffine.negY x y := by
    rw [Shimura.negY_AC, ← mul_assoc, I_mul_I]; ring
  rw [e1, e2] at h2
  exact (nonsingular_neg ..).1 h2

/-- **`φ(τ + 1/4) = [i]φ(τ)`**, on algebraic points. -/
theorem toC_iPt_of_quarter (τ τ' : UpperHalfPlane) (h : (τ' : ℂ) = τ + 1 / 4) (P : PtA)
    (hP : toC P = X0.phiC τ) : toC (iPt P) = X0.phiC τ' := by
  have hx : X0.xC τ' = -X0.xC τ := by rw [h, xC_add_quarter]
  have hy : X0.yC τ' = I * X0.yC τ := by rw [h, yC_add_quarter]
  unfold X0.phiC at hP ⊢
  by_cases hns : X0.curveAC.toAffine.Nonsingular (X0.xC τ) (X0.yC τ)
  · have hns' : X0.curveAC.toAffine.Nonsingular (X0.xC τ') (X0.yC τ') := by
      rw [hx, hy]; exact nonsingular_iC hns
    rw [dif_pos hns] at hP
    rw [dif_pos hns']
    rcases P with _ | ⟨x, y, hxy⟩
    · exact absurd hP (fun h => by cases h)
    · simp only [toC, Point.map_some, Point.some.injEq] at hP
      rw [iPt_some]
      simp only [toC, Point.map_some, Point.some.injEq]
      refine ⟨?_, ?_⟩
      · rw [hx, ← hP.1]; simp
      · rw [hy, ← hP.2, map_mul]
        congr 1
        exact ιC_iQ
  · have hns' : ¬ X0.curveAC.toAffine.Nonsingular (X0.xC τ') (X0.yC τ') := by
      rw [hx, hy]; exact fun h' => hns (nonsingular_iC_iff.1 h')
    rw [dif_neg hns] at hP
    rw [dif_neg hns']
    rcases P with _ | ⟨x, y, hxy⟩
    · rfl
    · exact absurd hP (fun h => by cases h)

theorem iPt_sub (P R : PtA) : iPt (P - R) = iPt P - iPt R := map_sub iHom P R

/-- The conjugate of TYZ's form. -/
def tbarK (n : ℕ) : QNeg n := ⟨-1 / (4 * (n + 1)), 1 / (4 * (n + 1))⟩

theorem tyzForm_conj_tau (n : ℕ) (hn : n % 8 = 5) :
    (tyzForm n hn).conj.tau = Shimura.kappa n (tbarK n) := by
  have h1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [HeegnerForm.tau, HeegnerForm.conj, cmPoint, tyzForm, Shimura.kappa, tbarK,
    Shimura.sqrt_64n]
  push_cast
  field_simp
  ring

theorem tbarK_mul (n : ℕ) [NeZero n] :
    tbarK n * (1 - 8 * Shimura.tauK n) = Shimura.tauK n := by
  have h1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  ext <;> simp [tbarK, Shimura.tauK, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;> field_simp <;> ring

/-- `τ_{Q̄} = W T₄ W τ_Q`. -/
theorem tyzForm_conj_tauH (n : ℕ) [NeZero n] (hn : n % 8 = 5) :
    ((tyzForm n hn).conj.tauH : ℂ) =
      ((Shimura.frickeH (quarterH (Shimura.frickeH (tyzForm n hn).tauH)) : UpperHalfPlane) : ℂ) := by
  have hτ : ((tyzForm n hn).tauH : ℂ) = Shimura.kappaAlg n (Shimura.tauK n) := by
    rw [Shimura.kappaAlg_apply, ← Shimura.tyzForm_tau n hn]; rfl
  have hτ' : ((tyzForm n hn).conj.tauH : ℂ) = Shimura.kappaAlg n (tbarK n) := by
    rw [Shimura.kappaAlg_apply, ← tyzForm_conj_tau n hn]; rfl
  have hrel := congrArg (Shimura.kappaAlg n) (tbarK_mul n)
  simp only [map_mul, map_sub, map_one, map_ofNat] at hrel
  rw [← hτ, ← hτ'] at hrel
  set τ := ((tyzForm n hn).tauH : ℂ)
  have hne : τ ≠ 0 := (tyzForm n hn).tauH.ne_zero
  have hne2 : (8 * τ - 1) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    exact (tyzForm n hn).tauH.im_pos.ne' this
  show _ = -1 / (32 * (-1 / (32 * τ) + 1 / 4))
  rw [show (32 : ℂ) * (-1 / (32 * τ) + 1 / 4) = (8 * τ - 1) / τ by field_simp; ring]
  rw [div_div_eq_mul_div, eq_div_iff hne2]
  linear_combination -hrel

/-- **`f₀(P_{Q̄}) = [i]f₀(P_n) + T − [i]T`** (given algebraicity of the Heegner point). -/
theorem heegnerPt_tyzForm_conj (hA : CMAlgebraic) (n : ℕ) [NeZero n] (hn : n % 8 = 5) :
    heegnerPt (tyzForm n hn).conj = ptT - iPt ptT + iPt (heegnerPt (tyzForm n hn)) := by
  set Q := tyzForm n hn
  obtain ⟨P, hP⟩ := hA _ Q
  rw [heegnerPt_eq Q hP]
  apply heegnerPt_eq
  set τ₁ := Shimura.frickeH Q.tauH
  set τ₂ := quarterH τ₁
  set τ₃ := Shimura.frickeH τ₂
  have hτ₃ : Q.conj.tauH = τ₃ := UpperHalfPlane.ext (tyzForm_conj_tauH n hn)
  have e1 : X0.phiC τ₁ + X0.phiC Q.tauH = X0.ptTC := Shimura.etaModelFricke Q.tauH τ₁ rfl
  have e3 : X0.phiC τ₃ + X0.phiC τ₂ = X0.ptTC := Shimura.etaModelFricke τ₂ τ₃ rfl
  have h1 : toC (ptT - P) = X0.phiC τ₁ := by
    rw [map_sub, toC_ptT, hP, ← e1]; abel
  have h2 : toC (iPt (ptT - P)) = X0.phiC τ₂ := toC_iPt_of_quarter τ₁ τ₂ rfl _ h1
  have h3 : toC (ptT - iPt (ptT - P)) = X0.phiC τ₃ := by
    rw [map_sub, toC_ptT, h2, ← e3]; abel
  rw [hτ₃, ← h3, iPt_sub]
  congr 1
  abel

theorem isComplexConj_apply_iQ {γ : GalQ} (hγ : IsComplexConj γ) : γ iQ = -iQ := by
  apply ιC_injective
  rw [hγ, ιC_iQ, map_neg, ιC_iQ, Complex.conj_I]

/-- **`TYZThm36ConjFive` from algebraicity of Heegner points** (x0-32's Fricke leaf is proved by
tyz-cm; `τ ↦ τ + 1/4` is proved here). -/
theorem tyzThm36ConjFive_of (hA : CMAlgebraic) : TYZThm36ConjFive := by
  intro n hn hsq γ hγ
  haveI : NeZero n := ⟨by omega⟩
  have hi := isComplexConj_apply_iQ hγ
  have hc : galPt γ (tyzHeegnerPt n) = ptT - iPt ptT + iPt (tyzHeegnerPt n) := by
    simp only [tyzHeegnerPt, hn, ↓reduceDIte]
    rw [cmComplexConj γ hγ, heegnerPt_tyzForm_conj hA n hn]
  have h2 : tauG 2 = ptT + ptT := by
    rw [← one_add_one_eq_two, map_add, tauG_apply, one_smul]
  simp only [tyzZn]
  rw [map_sub, galPt_iPt_of_neg hi, sub_neg_eq_add, hc, iPt_add, iPt_sub, iPt_iPt, iPt_iPt, h2]
  abel

end Conj

/-! ### `TYZThm36OneFive` from Shimura reciprocity (`𝔞`-action on TYZ's Heegner point)

With `𝔟 = 𝔞 ∩ O_{n,4} = ℤ⟨m, −4 + 4√−n⟩` (`m = (n+1)/2`, `idealMeetOrder_varpi`), `Q = [16(n+1), −8, 1]`
and `Q'' = [32(n+4), 8(n+2), m]` (`tyzFormW`): `τ_{Q''} = W(τ_Q + 1/4)` (`tyzFormW_tauH`) and
`𝔟·(⟨1,τ_{Q''}⟩, ⟨1/32,τ_{Q''}⟩) = c·(⟨1,τ_Q⟩, ⟨1/32,τ_Q⟩)`, `c = (−1 + ((n+3)/2)√−n)/(n+4)`
(`idealLat_varpi_mul`, `idealLat_varpi_mulN`; found and checked numerically for 10 values of `n` by
`scratch/tyz-321/wlat.py`, integer coefficients by `wcoef.py`). Shimura reciprocity
(`ShimuraReciprocityPic`) then gives `σ_w(f₀(P_n)) = f₀(P_{Q''}) = T − [i]f₀(P_n)`
(`heegnerPt_tyzFormW`, Fricke + `τ ↦ τ + 1/4`), and with `σ_w(i) = −i` (`WNegatesI`),
`σ_w(z_n) = z_n + τ((1+i)/2)`. -/

section WAction

open QuadraticAlgebra Pointwise WeierstrassCurve.Affine Complex

variable {n : ℕ} [NeZero n]

def hW0 (n : ℕ) : QNeg n := ⟨((n : ℚ) + 1) / 2, 0⟩
def hW1 (n : ℕ) : QNeg n := ⟨-4, 4⟩

@[simp] theorem hW0_re : (hW0 n).re = ((n : ℚ) + 1) / 2 := rfl
@[simp] theorem hW0_im : (hW0 n).im = 0 := rfl
@[simp] theorem hW1_re : (hW1 n).re = -4 := rfl
@[simp] theorem hW1_im : (hW1 n).im = 4 := rfl

theorem natCast_m (hn : n % 8 = 5) : (((n + 1) / 2 : ℕ) : ℚ) = ((n : ℚ) + 1) / 2 := by
  have : (n + 1) / 2 * 2 = n + 1 := by omega
  have h' : (((n + 1) / 2 : ℕ) : ℚ) * 2 = (n : ℚ) + 1 := by exact_mod_cast this
  linarith

theorem coe_m (hn : n % 8 = 5) :
    (((((n + 1) / 2 : ℕ) : 𝓞 (QNeg n))) : QNeg n) = hW0 n := by
  have h2 : (((n + 1) / 2 : ℕ) : ℚ) = ((n : ℚ) + 1) / 2 := by
    have : (n + 1) / 2 * 2 = n + 1 := by omega
    have h' : (((n + 1) / 2 : ℕ) : ℚ) * 2 = (n : ℚ) + 1 := by exact_mod_cast this
    linarith
  rw [show ((((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) : QNeg n) = (((n + 1) / 2 : ℕ) : QNeg n) from
    map_natCast (algebraMap (𝓞 (QNeg n)) (QNeg n)) _]
  ext
  · rw [QuadraticAlgebra.re_natCast, h2]; rfl
  · rw [QuadraticAlgebra.im_natCast]; rfl

theorem varpiIdeal_mem (hn : n % 8 = 5) :
    varpiIdeal n ∈ integralIdealsPrimeTo (O4 n).conductorModulus := by
  rw [Modulus.mem_integralIdealsPrimeTo, Modulus.isCoprimeTo_iff_sup_eq_top,
    conductorModulus_finitePart]
  have key : (1 : 𝓞 (QNeg n)) = (-1) * (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) +
      4 * (((n + 3) / 8 : ℕ) : 𝓞 (QNeg n)) := by
    have h' : (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) + 1 = 4 * (((n + 3) / 8 : ℕ) : 𝓞 (QNeg n)) := by
      exact_mod_cast (show (n + 1) / 2 + 1 = 4 * ((n + 3) / 8) by omega)
    linear_combination h'
  refine ⟨?_, ?_⟩
  · intro h
    have hmem : (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) ∈ varpiIdeal n :=
      Ideal.subset_span (Set.mem_insert _ _)
    rw [h, Ideal.mem_bot] at hmem
    have h2 := congrArg (fun x : 𝓞 (QNeg n) => ((x : QNeg n)).re) hmem
    simp only [coe_m hn, hW0] at h2
    simp at h2
    have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
    linarith
  · rw [Ideal.eq_top_iff_one, key]
    refine Ideal.add_mem _ (Ideal.mem_sup_left
      (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))) (Ideal.mem_sup_right ?_)
    simpa using natCast_mul_mem_conductor (QNeg n) 4 ((((n + 3) / 8 : ℕ)) : 𝓞 (QNeg n))

theorem wClass_eq (hn : n % 8 = 5) : wClass n = (O4 n).picClass ⟨_, varpiIdeal_mem hn⟩ := by
  unfold wClass; rw [dif_pos (varpiIdeal_mem hn)]

theorem idealMeetOrder_varpi (hn : n % 8 = 5) (hsq : Squarefree n) :
    Shimura.idealMeetOrder n 4 (varpiIdeal n) =
      (Submodule.span ℤ ({hW0 n, hW1 n} : Set (QNeg n)) : Set (QNeg n)) := by
  have hn4 : n % 4 = 1 := by omega
  have hmq := natCast_m hn
  unfold varpiIdeal
  generalize (n + 1) / 2 = m at hmq ⊢
  have hcm : ((m : 𝓞 (QNeg n)) : QNeg n) = hW0 n := by
    rw [show ((m : 𝓞 (QNeg n)) : QNeg n) = (m : QNeg n) from
      map_natCast (algebraMap (𝓞 (QNeg n)) (QNeg n)) _]
    ext
    · rw [QuadraticAlgebra.re_natCast, hmq]; rfl
    · rw [QuadraticAlgebra.im_natCast]; rfl
  ext x
  simp only [Shimura.idealMeetOrder, Set.mem_ofPred_eq, SetLike.mem_coe, Submodule.mem_span_pair,
    Shimura.mem_O4_iff']
  constructor
  · rintro ⟨⟨c, z, hz⟩, y, hy, rfl⟩
    obtain ⟨a, b, hab⟩ := hy
    simp only [smul_eq_mul] at hab
    obtain ⟨a1, a2, ha1, ha2⟩ := Shimura.int_coords hn4 hsq a
    obtain ⟨b1, b2, hb1, hb2⟩ := Shimura.int_coords hn4 hsq b
    obtain ⟨p, q, hp, hq⟩ := Shimura.int_coords hn4 hsq z
    have hy' : (y : QNeg n) = (a : QNeg n) * hW0 n + (b : QNeg n) * (QuadraticAlgebra.omega - 1) := by
      rw [← hab]; push_cast [hcm, coe_sqrtNeg]; rfl
    have him := congrArg QuadraticAlgebra.im hz
    rw [hy'] at him
    simp [ha1, ha2, hb1, hb2, hp, hq] at him
    refine ⟨a1 + a2 - 2 * b2, q, ?_⟩
    rw [hy']
    ext
    · simp [ha1, ha2, hb1, hb2]
      linear_combination him
    · simp [ha1, ha2, hb1, hb2]
      linear_combination -him
  · rintro ⟨P, Q, rfl⟩
    refine ⟨⟨P * m - 4 * Q, (Q : 𝓞 (QNeg n)) * sqrtNeg n, ?_⟩,
      (P : 𝓞 (QNeg n)) * (m : 𝓞 (QNeg n)) + ((4 * Q : ℤ) : 𝓞 (QNeg n)) * (sqrtNeg n - 1), ?_, ?_⟩
    · ext
      · simp [hmq, coe_sqrtNeg]
        ring
      · simp [hmq, coe_sqrtNeg]
        ring
    · exact ⟨_, _, rfl⟩
    · ext
      · simp [hmq, coe_sqrtNeg, map_ofNat]
        ring
      · simp [hmq, coe_sqrtNeg, map_ofNat]
        ring

/-- **`Q'' = [32(n+4), 8(n+2), (n+1)/2]`**, a Heegner form of level 32 and discriminant `−64n`, with
`τ_{Q''} = W(τ_Q + 1/4)`. -/
def tyzFormW (n : ℕ) (hn : n % 8 = 5) : HeegnerForm 32 (-64 * n) where
  A := 32 * (n + 4)
  B := 8 * (n + 2)
  C := (((n + 1) / 2 : ℕ) : ℤ)
  A_pos := by positivity
  N_dvd := ⟨n + 4, by push_cast; ring⟩
  disc := by
    have h2 : (((n + 1) / 2 : ℕ) : ℤ) * 2 = n + 1 := by omega
    linear_combination (-64 * ((n : ℤ) + 4)) * h2
  D_neg := by
    have : (0 : ℤ) < n := by omega
    linarith
  primitive := by
    set g := Int.gcd (Int.gcd (32 * ((n : ℤ) + 4)) (8 * ((n : ℤ) + 2))) (((n + 1) / 2 : ℕ) : ℤ)
    have hB : (g : ℤ) ∣ 8 * ((n : ℤ) + 2) := (Int.gcd_dvd_left ..).trans (Int.gcd_dvd_right ..)
    have hC : (g : ℤ) ∣ (((n + 1) / 2 : ℕ) : ℤ) := Int.gcd_dvd_right ..
    have hCk : (((n + 1) / 2 : ℕ) : ℤ) = 4 * ((n / 8 : ℕ) : ℤ) + 3 := by omega
    have hnk : (n : ℤ) = 8 * ((n / 8 : ℕ) : ℤ) + 5 := by omega
    rw [hCk] at hC
    rw [hnk] at hB
    have h1 : (g : ℤ) ∣ 1 := by
      have e : (1 : ℤ) = (4 * ((n / 8 : ℕ) : ℤ) + 3) * (4 * ((n / 8 : ℕ) : ℤ) + 3 +
          16 * (2 * ((n / 8 : ℕ) : ℤ) + 1) * ((n / 8 : ℕ) + 1)) -
          (2 * ((n / 8 : ℕ) : ℤ) + 1) * ((n / 8 : ℕ) + 1) * (8 * (8 * ((n / 8 : ℕ) : ℤ) + 5 + 2)) := by
        ring
      rw [e]
      exact dvd_sub (dvd_mul_of_dvd_left hC _) (dvd_mul_of_dvd_right hB _)
    exact Nat.dvd_one.mp (by exact_mod_cast h1)

/-- `τ_{Q''} = (−(n+2) + √−n)/(8(n+4))`. -/
def tauW (n : ℕ) : QNeg n := ⟨-((n : ℚ) + 2) / (8 * (n + 4)), 1 / (8 * (n + 4))⟩
/-- The homothety factor `c = (−1 + ((n+3)/2)√−n)/(n+4)`. -/
def cW (n : ℕ) : QNeg n := ⟨-1 / ((n : ℚ) + 4), ((n : ℚ) + 3) / 2 / (n + 4)⟩

theorem tyzFormW_tau (n : ℕ) (hn : n % 8 = 5) : (tyzFormW n hn).tau = Shimura.kappa n (tauW n) := by
  have h4 : ((n : ℂ) + 4) ≠ 0 := by exact_mod_cast (show n + 4 ≠ 0 by omega)
  simp only [HeegnerForm.tau, cmPoint, tyzFormW, Shimura.kappa, tauW, Shimura.sqrt_64n]
  push_cast
  field_simp
  ring

theorem tauW_mul (n : ℕ) [NeZero n] : tauW n * (32 * Shimura.tauK n + 8) = -1 := by
  have h1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have h4 : ((n : ℚ) + 4) ≠ 0 := by positivity
  ext <;> simp [tauW, Shimura.tauK, QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat] <;>
    field_simp <;> ring

omit [NeZero n] in
@[simp] theorem tauW_re : (tauW n).re = -((n : ℚ) + 2) / (8 * (n + 4)) := rfl
omit [NeZero n] in
@[simp] theorem tauW_im : (tauW n).im = 1 / (8 * ((n : ℚ) + 4)) := rfl
omit [NeZero n] in
@[simp] theorem cW_re : (cW n).re = -1 / ((n : ℚ) + 4) := rfl
omit [NeZero n] in
@[simp] theorem cW_im : (cW n).im = ((n : ℚ) + 3) / 2 / (n + 4) := rfl
omit [NeZero n] in
@[simp] theorem tauK_re : (Shimura.tauK n).re = 1 / (4 * ((n : ℚ) + 1)) := rfl
omit [NeZero n] in
@[simp] theorem tauK_im : (Shimura.tauK n).im = 1 / (4 * ((n : ℚ) + 1)) := rfl

theorem latKW (k : ℕ) (hk : n = 8 * k + 5) :
    Submodule.span ℤ ({hW0 n, hW1 n} : Set (QNeg n)) * Submodule.span ℤ {1, tauW n} =
      Submodule.span ℤ {cW n * 1, cW n * Shimura.tauK n} := by
  subst hk
  have h1 : (8 * (k : ℚ) + 5 + 1) ≠ 0 := by positivity
  have h4 : (8 * (k : ℚ) + 5 + 4) ≠ 0 := by positivity
  rw [Submodule.span_mul_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, t, ht, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact Shimura.mem_span_pair_of 1 (-32 - 32 * k) (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_pair_of 0 (3 + 4 * k) (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_pair_of 8 32 (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_pair_of (-1) 0 (by ext <;> simp <;> field_simp <;> ring)
  · rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact Shimura.mem_span_mul_four (hW0 _) (hW1 _) 1 (tauW _) (by simp) (by simp) (by simp)
        (by simp) 0 0 0 (-1) (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_mul_four (hW0 _) (hW1 _) 1 (tauW _) (by simp) (by simp) (by simp)
        (by simp) 0 (11 - 484 * k + 21296 * (k * k)) (-(1 - 44 * k + 1936 * (k * k) + 2662 * (k * k * k)))
        (8 * (-(1 - 44 * k + 1936 * (k * k) + 2662 * (k * k * k))))
        (by ext <;> simp <;> field_simp <;> ring)

theorem latNKW (k : ℕ) (hk : n = 8 * k + 5) :
    Submodule.span ℤ ({hW0 n, hW1 n} : Set (QNeg n)) * Submodule.span ℤ {Shimura.oneN n, tauW n} =
      Submodule.span ℤ {cW n * Shimura.oneN n, cW n * Shimura.tauK n} := by
  subst hk
  have h1 : (8 * (k : ℚ) + 5 + 1) ≠ 0 := by positivity
  have h4 : (8 * (k : ℚ) + 5 + 4) ≠ 0 := by positivity
  rw [Submodule.span_mul_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, t, ht, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl
    · exact Shimura.mem_span_pair_of 1 (-1 - k) (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_pair_of 0 (3 + 4 * k) (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_pair_of 8 1 (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_pair_of (-32) 0 (by ext <;> simp <;> field_simp <;> ring)
  · rw [Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact Shimura.mem_span_mul_four (hW0 _) (hW1 _) (Shimura.oneN _) (tauW _) (by simp) (by simp)
        (by simp) (by simp) 1 (3 * (k + 1)) (-4 * (k + 1) * (3 * k + 2)) (-(k + 1) * (3 * k + 2))
        (by ext <;> simp <;> field_simp <;> ring)
    · exact Shimura.mem_span_mul_four (hW0 _) (hW1 _) (Shimura.oneN _) (tauW _) (by simp) (by simp)
        (by simp) (by simp) 0 3 (-12 * k - 8) (-3 * k - 2)
        (by ext <;> simp <;> field_simp <;> ring)




theorem idealLat_varpi (hn : n % 8 = 5) (hsq : Squarefree n) :
    Shimura.idealLat n 4 (varpiIdeal n) = (Submodule.span ℤ {hW0 n, hW1 n}).map (Shimura.kappaLin n) := by
  rw [Shimura.idealLat, idealMeetOrder_varpi hn hsq,
    show Shimura.kappa n = Shimura.kappaLin n from funext fun x => (Shimura.kappaLin_apply n x).symm,
    Submodule.span_image, Submodule.span_eq]

theorem idealLat_varpi_mul (hn : n % 8 = 5) (hsq : Squarefree n) :
    Shimura.idealLat n 4 (varpiIdeal n) * (tyzFormW n hn).lat =
      (tyzForm n hn).lat.map (LinearMap.mulLeft ℤ (Shimura.kappa n (cW n))) := by
  rw [idealLat_varpi hn hsq, Shimura.lat_eq_map _ n _ (tyzFormW_tau n hn),
    Shimura.lat_eq_map _ n _ (Shimura.tyzForm_tau n hn), Shimura.map_mulLeft_span_pair,
    Shimura.kappaLin, ← Submodule.map_mul, latKW (n / 8) (by omega)]

theorem idealLat_varpi_mulN (hn : n % 8 = 5) (hsq : Squarefree n) :
    Shimura.idealLat n 4 (varpiIdeal n) * (tyzFormW n hn).latN =
      (tyzForm n hn).latN.map (LinearMap.mulLeft ℤ (Shimura.kappa n (cW n))) := by
  rw [idealLat_varpi hn hsq, Shimura.latN_eq_map _ n _ (tyzFormW_tau n hn),
    Shimura.latN_eq_map _ n _ (Shimura.tyzForm_tau n hn), Shimura.map_mulLeft_span_pair,
    Shimura.kappaLin, ← Submodule.map_mul, latNKW (n / 8) (by omega)]

/-- `τ_{Q''} = W(τ_Q + 1/4)`. -/
theorem tyzFormW_tauH (hn : n % 8 = 5) :
    ((tyzFormW n hn).tauH : ℂ) =
      ((Shimura.frickeH (quarterH (tyzForm n hn).tauH) : UpperHalfPlane) : ℂ) := by
  have hτ : ((tyzForm n hn).tauH : ℂ) = Shimura.kappaAlg n (Shimura.tauK n) := by
    rw [Shimura.kappaAlg_apply, ← Shimura.tyzForm_tau n hn]; rfl
  have hτ' : ((tyzFormW n hn).tauH : ℂ) = Shimura.kappaAlg n (tauW n) := by
    rw [Shimura.kappaAlg_apply, ← tyzFormW_tau n hn]; rfl
  have hrel := congrArg (Shimura.kappaAlg n) (tauW_mul n)
  simp only [map_mul, map_add, map_neg, map_one, map_ofNat] at hrel
  rw [← hτ, ← hτ'] at hrel
  set τ := ((tyzForm n hn).tauH : ℂ)
  have hne : (32 * (τ + 1 / 4)) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp at this
    exact (tyzForm n hn).tauH.im_pos.ne' this
  show _ = -1 / (32 * (τ + 1 / 4))
  rw [eq_div_iff hne]
  linear_combination hrel

/-- **`f₀(P_{Q''}) = T − [i]f₀(P_n)`** (given algebraicity of the Heegner point). -/
theorem heegnerPt_tyzFormW (hA : CMAlgebraic) (hn : n % 8 = 5) :
    heegnerPt (tyzFormW n hn) = ptT - iPt (heegnerPt (tyzForm n hn)) := by
  set Q := tyzForm n hn
  obtain ⟨P, hP⟩ := hA _ Q
  rw [heegnerPt_eq Q hP]
  apply heegnerPt_eq
  set τ₁ := quarterH Q.tauH
  set τ₂ := Shimura.frickeH τ₁
  have hτ₂ : (tyzFormW n hn).tauH = τ₂ := UpperHalfPlane.ext (tyzFormW_tauH hn)
  have e2 : X0.phiC τ₂ + X0.phiC τ₁ = X0.ptTC := Shimura.etaModelFricke τ₁ τ₂ rfl
  have h1 : toC (iPt P) = X0.phiC τ₁ := toC_iPt_of_quarter Q.tauH τ₁ rfl _ hP
  rw [hτ₂, map_sub, toC_ptT, h1, ← e2]
  abel

theorem acts4_inv {ρ : GalQ} {c : Pic (O4 n)} (hρ : ActsAsArtin4 ρ n c) :
    ActsAsArtin4 ρ⁻¹ n c⁻¹ := by
  intro x
  have e : artin4 n c (artin4 n c⁻¹ x) = x := by
    rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  have h := hρ (artin4 n c⁻¹ x)
  rw [e] at h
  calc ρ⁻¹ (embed n (x : SeparableClosure (QNeg n)))
      = ρ⁻¹ (ρ (embed n ((artin4 n c⁻¹ x : H4 n) : SeparableClosure (QNeg n)))) := by rw [h]
    _ = _ := ρ.symm_apply_apply _

set_option maxRecDepth 10000 in
/-- `ρ` acting on `H_{n,4}` as `c` (through `embed n`) acts as `c` through an embedding normalized by
`ιC(e(√−n)) = i√n`, either directly or after inverting `ρ`. -/
theorem normalized_cases {c : Pic (O4 n)} {ρ : GalQ} (hρ : ActsAsArtin4 ρ n c) :
    ∃ e : SeparableClosure (QNeg n) →ₐ[ℚ] Qbar,
      ιC (e (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)) =
        I * (Real.sqrt n : ℂ) ∧
      ((∀ x : ringClassField (conductorOrder (QNeg n) 4),
        ρ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg n) 4) c x)) ∨
      (∀ x : ringClassField (conductorOrder (QNeg n) 4),
        ρ⁻¹ (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg n) 4) c x))) := by
  set r := embed n (algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega)
  have hr : r ^ 2 = -(n : Qbar) := by
    simp only [r, ← map_pow, Shimura.omega_sq', map_neg, map_natCast]
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hC : ιC r ^ 2 = (I * (Real.sqrt n : ℂ)) ^ 2 := by
    rw [← map_pow, hr, mul_pow, I_sq, sq, Shimura.sqrt_mul_self_C]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hC with h | h
  · exact ⟨embed n, h, Or.inl hρ⟩
  · obtain ⟨γ, hγ⟩ := Shimura.exists_galQ_neg hn0 hr
    have hr0 : r ≠ 0 := by
      intro h0; rw [h0] at hr
      have : (n : Qbar) = 0 := by linear_combination hr
      exact NeZero.ne n (by exact_mod_cast this)
    have hγinv : γ⁻¹ r = -r := by
      apply γ.injective
      show γ (γ.symm r) = γ (-r)
      rw [AlgEquiv.apply_symm_apply, map_neg, hγ, neg_neg]
    have hne : γ⁻¹ r ≠ r := by
      rw [hγinv]; intro h'
      apply hr0
      have : (2 : Qbar) * r = 0 := by linear_combination -h'
      simpa using this
    have hconj := RingClassBridge.actsAsArtin4_conj (γ := γ⁻¹) hne (acts4_inv hρ)
    rw [inv_inv, inv_inv] at hconj
    refine ⟨γ.toAlgHom.comp (embed n), ?_, Or.inr fun x => ?_⟩
    · show ιC (γ r) = _
      rw [hγ, map_neg, h, neg_neg]
    · have h1 := hconj x
      simp only [AlgEquiv.mul_apply] at h1
      show ρ⁻¹ (γ (embed n (x : SeparableClosure (QNeg n)))) = γ (embed n _)
      rw [← h1]; exact (γ.apply_symm_apply _).symm

theorem galPt_one (P : PtA) : galPt 1 P = P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · obtain ⟨h', e'⟩ := galPt_some 1 h
    rw [e']
    rfl

theorem galPt_tauG_one_one_of_neg {ρ : GalQ} (hρ : ρ iQ = -iQ) :
    galPt ρ (tauG ⟨1, 1⟩) = tauG ⟨1, -1⟩ := by
  rw [tauG_mk, tauG_mk, map_add, one_smul, one_smul, galPt_ptT, galPt_iPt_of_neg hρ, galPt_ptT,
    neg_one_zsmul]

/-- **`TYZThm36OneFive` from Shimura reciprocity, algebraicity and `WNegatesI`.** -/
theorem tyzThm36OneFive_of (hS : Shimura.ShimuraReciprocityPic) (hA : CMAlgebraic)
    (hneg : WNegatesI) : TYZThm36OneFive := by
  intro n hn0 hn hsq ρ hρ
  have hi := hneg n hn0 hn hsq ρ hρ
  have hD : -64 * (n : ℤ) = Shimura.discOf n 4 := by
    rw [Shimura.discOf, ite_eq_right (by omega)]; push_cast; ring
  rw [wClass_eq hn] at hρ
  obtain ⟨e, he, hcase⟩ := normalized_cases hρ
  have key : ∀ ρ' : GalQ, ρ' iQ = -iQ → (∀ x : ringClassField (conductorOrder (QNeg n) 4),
      ρ' (e x) = e (ringClassArtinEquiv (conductorOrder (QNeg n) 4)
        ((O4 n).picClass ⟨_, varpiIdeal_mem hn⟩) x)) →
      galPt ρ' (tyzZn n) = tyzZn n + tauG ⟨1, 1⟩ := by
    intro ρ' hi' hρ'
    have hrec := hS n 4 hsq e he ⟨_, varpiIdeal_mem hn⟩ ρ' hρ' (-64 * n) hD (tyzForm n hn)
      (tyzFormW n hn) (Shimura.kappa n (cW n)) (idealLat_varpi_mul hn hsq)
      (idealLat_varpi_mulN hn hsq)
    rw [heegnerPt_tyzFormW hA hn] at hrec
    simp only [tyzZn, tyzHeegnerPt, hn, ↓reduceDIte]
    rw [map_sub, galPt_iPt_of_neg hi', hrec, sub_neg_eq_add, iPt_sub, iPt_iPt, tauG_mk, one_smul,
      one_smul]
    abel
  rcases hcase with h | h
  · exact ⟨0, by rw [key ρ hi h, zero_zsmul, add_zero]⟩
  · have hi' : ρ⁻¹ iQ = -iQ := by
      apply ρ.injective
      rw [show ρ (ρ⁻¹ iQ) = iQ from ρ.apply_symm_apply iQ, map_neg, hi, neg_neg]
    have h1 := key ρ⁻¹ hi' h
    have h2 : galPt ρ (galPt ρ⁻¹ (tyzZn n)) = tyzZn n := by
      rw [← galPt_mul, mul_inv_cancel, galPt_one]
    rw [h1, map_add, galPt_tauG_one_one_of_neg hi] at h2
    have h11 := tauG_one_one_add
    refine ⟨-1, ?_⟩
    rw [neg_one_zsmul, ← h11, eq_sub_of_add_eq h2]
    abel

end WAction

/-! ### Genus characters as Artin characters for odd `n` (port of cm-bridge §13 "GT-ART") -/

section ArtinChiOdd

open ZInQ.RouteK.Redei IsDedekindDomain
open scoped nonZeroDivisors

variable {n : ℕ} [NeZero n]

/-- Away from `2n`: `𝔭` splits in the fixed field of `ker χ_q` iff it splits in `K_n(√q*)`. -/
theorem splitSet_kerChi_iff_odd (hodd : Odd n) (hsq : Squarefree n) (q : n.primeFactors)
    (𝔭 : HeightOneSpectrum (𝓞 (QNeg n)))
    (hT1 : ¬ (conductorOrder (QNeg n) 1).conductor ≤ 𝔭.asIdeal)
    (h2n : ((2 * n : ℕ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal) :
    𝔭 ∈ splitSet (QNeg n) (maxSubfield (kerChi q)) ↔
      𝔭 ∈ splitSet (QNeg n) (adjSqrt (QNeg n) (pstar q)) := by
  have hJ := mem_primeTo_max 𝔭 hT1
  have : ((⟨𝔭.asIdeal, hJ⟩ : integralIdealsPrimeTo (OK n).conductorModulus) :
    Ideal (𝓞 (QNeg n))).IsMaximal := 𝔭.isMaximal
  have hqp := Nat.prime_of_mem_primeFactors q.2
  have hq2 : (q : ℕ) ≠ 2 := by
    intro h
    have := Nat.dvd_of_mem_primeFactors q.2
    rw [h] at this
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 this)
  have h2a : ((2 * pstar q : ℤ) : 𝓞 (QNeg n)) ∉ 𝔭.asIdeal := by
    intro h; apply h2n
    obtain ⟨n', hn'⟩ := Nat.dvd_of_mem_primeFactors q.2
    have e2 : 2 * n = 2 * (q : ℕ) * n' := by rw [mul_assoc, ← hn']
    have hcast : ((2 * n : ℕ) : 𝓞 (QNeg n)) =
        ((2 * pstar q : ℤ) : 𝓞 (QNeg n)) *
          ((if (q : ℕ) % 4 = 1 then 1 else -1 : ℤ) * n' : 𝓞 (QNeg n)) := by
      rw [congrArg (Nat.cast (R := 𝓞 (QNeg n))) e2]
      unfold pstar
      split_ifs <;> push_cast <;> ring
    rw [hcast]
    exact 𝔭.asIdeal.mul_mem_right _ h
  rw [mem_splitSet_iff (OK n) _ ⟨_, hJ⟩ 𝔭 rfl]
  change chi n q ((OK n).picClass ⟨_, hJ⟩) = 1 ↔ _
  rw [picClass_maximal ⟨_, hJ⟩ (mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot),
    mem_splitSet_adjSqrt_iff 𝔭 h2a]
  have := Fact.mk hqp
  letI := Ideal.Quotient.field 𝔭.asIdeal
  haveI : Finite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient 𝔭.ne_bot
  letI := Fintype.ofFinite (𝓞 (QNeg n) ⧸ 𝔭.asIdeal)
  obtain ⟨hchar, hcharq⟩ := residue_facts 𝔭 h2n q.2
  have hN : Ideal.absNorm 𝔭.asIdeal = Fintype.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hqN : ¬ (q : ℕ) ∣ Ideal.absNorm 𝔭.asIdeal := by
    rw [hN]
    intro hd
    obtain ⟨k, hk, hcard⟩ := FiniteField.card (𝓞 (QNeg n) ⧸ 𝔭.asIdeal)
      (ringChar (𝓞 (QNeg n) ⧸ 𝔭.asIdeal))
    rw [hcard] at hd
    exact hcharq ((Nat.prime_dvd_prime_iff_eq hqp hk).1 (hqp.dvd_of_dvd_pow hd)).symm
  have hc := chi_mk0 n hodd hsq q ⟨𝔭.asIdeal, mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot⟩ hqN
  rw [hc, isSquare_pstar_iff hchar hq2 hcharq]
  unfold ZInQ.RouteK.legBit
  rw [hN, Int.cast_natCast]
  split_ifs with h
  · simp only [ofAdd_zero, true_iff]; exact h
  · simp only [h, iff_false]; decide

/-- **The fixed field of `ker χ_q` is `K_n(√q*)`** (Bauer, both directions). -/
theorem maxSubfield_kerChi_odd (hodd : Odd n) (hsq : Squarefree n) (q : n.primeFactors) :
    maxSubfield (kerChi q) = adjSqrt (QNeg n) (pstar q) := by
  have hI : (conductorOrder (QNeg n) 1).conductor * Ideal.span {((2 * n : ℕ) : 𝓞 (QNeg n))} ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or]
    refine ⟨(conductorOrder (QNeg n) 1).conductor_ne_bot, ?_⟩
    rw [Ideal.span_singleton_eq_bot]
    exact_mod_cast (show 2 * n ≠ 0 by have := NeZero.ne n; omega)
  have key : ∀ 𝔭 : HeightOneSpectrum (𝓞 (QNeg n)),
      𝔭 ∉ {𝔭 : HeightOneSpectrum (𝓞 (QNeg n)) | (conductorOrder (QNeg n) 1).conductor *
        Ideal.span {((2 * n : ℕ) : 𝓞 (QNeg n))} ≤ 𝔭.asIdeal} →
      (𝔭 ∈ splitSet (QNeg n) (maxSubfield (kerChi q)) ↔
        𝔭 ∈ splitSet (QNeg n) (adjSqrt (QNeg n) (pstar q))) := fun 𝔭 hT =>
    splitSet_kerChi_iff_odd hodd hsq q 𝔭 (fun h => hT (le_trans Ideal.mul_le_left h))
      (fun h => hT (le_trans Ideal.mul_le_right ((Ideal.span_singleton_le_iff_mem _).2 h)))
  apply le_antisymm
  · exact le_of_splitSet_diff_subset _ (finite_le_primes _ hI)
      fun 𝔭 ⟨h𝔭, hT⟩ => (key 𝔭 hT).2 h𝔭
  · exact le_of_splitSet_diff_subset _ (finite_le_primes _ hI)
      fun 𝔭 ⟨h𝔭, hT⟩ => (key 𝔭 hT).1 h𝔭

/-- **Genus characters as Artin characters, any odd squarefree `n`** (cm-bridge's `artinPstarChi`
with `n ≡ 3 (mod 4)` replaced by `n` odd; same proof). -/
theorem artinPstarChi_odd (hodd : Odd n) (hsq : Squarefree n) (q : n.primeFactors) (c : Pic (OK n))
    (hs : sqrtK (QNeg n) (pstar q) ∈ hilbertField n) :
    ((ringClassArtinEquiv (OK n) c ⟨_, hs⟩ : hilbertField n) : SeparableClosure (QNeg n)) =
      (if chi n q c = 1 then 1 else -1) * sqrtK (QNeg n) (pstar q) := by
  set s := sqrtK (QNeg n) (pstar q)
  set g := ringClassArtinEquiv (OK n) c
  set s' : hilbertField n := ⟨s, hs⟩
  have hs2 : s' ^ 2 = algebraMap (QNeg n) (hilbertField n) ((pstar q : ℤ) : QNeg n) := by
    apply Subtype.ext
    show s ^ 2 = algebraMap (QNeg n) (SeparableClosure (QNeg n)) ((pstar q : ℤ) : QNeg n)
    rw [sqrtK_sq, map_intCast]
  have hg2 : ((g s' : hilbertField n) : SeparableClosure (QNeg n)) ^ 2 = s ^ 2 := by
    have h0 : (g s') ^ 2 = algebraMap (QNeg n) (hilbertField n) ((pstar q : ℤ) : QNeg n) := by
      rw [← map_pow, hs2, AlgEquiv.commutes]
    have h' := congrArg Subtype.val h0
    change ((g s' : hilbertField n) : SeparableClosure (QNeg n)) ^ 2 =
      algebraMap (QNeg n) (SeparableClosure (QNeg n)) ((pstar q : ℤ) : QNeg n) at h'
    rw [h', map_intCast, sqrtK_sq]
  have hmemE : s ∈ maxSubfield (kerChi q) := by
    rw [maxSubfield_kerChi_odd hodd hsq q]; exact IntermediateField.mem_adjoin_simple_self _ _
  have hfix_iff : g s' = s' ↔ chi n q c = 1 := by
    constructor
    · intro hfix
      have hle : adjSqrt (QNeg n) (pstar q) ≤
          IntermediateField.lift (IntermediateField.fixedField (Subgroup.zpowers g)) := by
        rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
        exact mem_lift_fixedField_zpowers g s' hfix
      rw [← maxSubfield_kerChi_odd hodd hsq q] at hle
      have hle' : IntermediateField.fixedField ((kerChi q).map (ringClassArtinEquiv (OK n)).toMonoidHom) ≤
          IntermediateField.fixedField (Subgroup.zpowers g) := fun x hx =>
        (IntermediateField.mem_lift x).1 (hle ((IntermediateField.mem_lift x).2 hx))
      have hZ : Subgroup.zpowers g ≤ (kerChi q).map (ringClassArtinEquiv (OK n)).toMonoidHom := by
        rw [← IntermediateField.fixingSubgroup_fixedField
          ((kerChi q).map (ringClassArtinEquiv (OK n)).toMonoidHom)]
        exact (IntermediateField.le_iff_le _ _).1 (le_trans hle' le_rfl)
      obtain ⟨c', hc', hce⟩ := Subgroup.mem_map.1 (hZ (Subgroup.mem_zpowers g))
      rw [(ringClassArtinEquiv (OK n)).injective hce] at hc'
      exact hc'
    · intro hc
      have h1 := (IntermediateField.mem_lift s').1 hmemE
      rw [IntermediateField.mem_fixedField_iff] at h1
      exact h1 g (Subgroup.mem_map_of_mem _ hc)
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hg2 with h | h
  · have hc : chi n q c = 1 := hfix_iff.1 (Subtype.ext h)
    rw [h, if_pos hc, one_mul]
  · have hc : chi n q c ≠ 1 := by
      intro hc
      have h' := congrArg Subtype.val (hfix_iff.2 hc)
      rw [h] at h'
      have h2 : (2 : SeparableClosure (QNeg n)) * s = 0 := by
        change -s = s at h'; linear_combination -h'
      have hs0 : s ≠ 0 := by
        intro h0
        have := sqrtK_sq (QNeg n) (pstar q)
        rw [← show s = sqrtK (QNeg n) (pstar q) from rfl, h0] at this
        have hp0 : pstar q ≠ 0 := by
          unfold pstar; split_ifs <;> simp [(Nat.prime_of_mem_primeFactors q.2).ne_zero]
        simp at this
        exact hp0 (by exact_mod_cast this.symm)
      rcases mul_eq_zero.1 h2 with h2 | h2
      · exact two_ne_zero h2
      · exact hs0 h2
    rw [h, if_neg hc]; ring

end ArtinChiOdd

/-! ### Genus theory for class 5: `WNegatesI` and `BetaOnGenus5`

`w = [𝔞]`, `𝔞𝔭₂ = (√−n − 1)`, `𝔭₂² = (2)` (`a_mul_p2`, `p2_sq`), so `χ_q(w) = χ_q([𝔭₂]) = (2/q)`
(`chi_wClass`). By the port of cm-bridge's GT-ART (`artinPstarChi_odd`) the Artin symbol of `c`
acts on `√q*` by `χ_q(c)`; `√−1 = ±√−n / Π_q √q*` gives `σ_w(i) = Π_q (2/q) i = (2/n) i = −i`, and
`σγ⁻¹` acts on `√q*` by `(−2, q*)_2 = (2/q)`, so `χ_q(σγ⁻¹) = χ_q(w)` for all `q` and
`[σγ⁻¹]w⁻¹ ∈ Cl² = ⋂_q ker χ_q` (`picSquares_eq_iInf_ker_chi`, Gauss). -/

section Genus5

open ZInQ.RouteK.Redei IsDedekindDomain
open scoped nonZeroDivisors

variable {n : ℕ} [NeZero n]

/-- The ramified prime `𝔭₂ = (2, √−n − 1)` of `𝓞_{K_n}` (`n ≡ 1 (mod 4)`). -/
def p2Ideal5 (n : ℕ) [NeZero n] : Ideal (𝓞 (QNeg n)) := Ideal.span {2, sqrtNeg n - 1}

theorem varpi_sq_add (n : ℕ) [NeZero n] :
    (sqrtNeg n - 1) * (sqrtNeg n - 1) + 2 * (sqrtNeg n - 1) = -((n : 𝓞 (QNeg n)) + 1) := by
  linear_combination sqrtNeg_mul_self (d := n)

theorem p2_sq (hn : n % 8 = 5) : p2Ideal5 n * p2Ideal5 n = Ideal.span {2} := by
  rw [p2Ideal5, Ideal.span_pair_mul_span_pair]
  have hv := varpi_sq_add n
  have hk : (n : 𝓞 (QNeg n)) + 1 = 8 * ((n / 8 : ℕ) : 𝓞 (QNeg n)) + 6 := by
    have : n + 1 = 8 * (n / 8) + 6 := by omega
    exact_mod_cast this
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨2, by ring⟩
    · exact ⟨sqrtNeg n - 1, rfl⟩
    · exact ⟨sqrtNeg n - 1, by ring⟩
    · exact ⟨-(4 * ((n / 8 : ℕ) : 𝓞 (QNeg n)) + 3) - (sqrtNeg n - 1), by linear_combination hv - hk⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    set S : Set (𝓞 (QNeg n)) := {2 * 2, 2 * (sqrtNeg n - 1), (sqrtNeg n - 1) * 2,
      (sqrtNeg n - 1) * (sqrtNeg n - 1)} with hS
    have e : (2 : 𝓞 (QNeg n)) = (-1) * ((sqrtNeg n - 1) * (sqrtNeg n - 1)) +
        (-1) * (2 * (sqrtNeg n - 1)) + (-(2 * ((n / 8 : ℕ) : 𝓞 (QNeg n)) + 1)) * (2 * 2) := by
      linear_combination hv - hk
    rw [e]
    refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_))
      (Ideal.mul_mem_left _ _ ?_)
    · exact Ideal.subset_span (by rw [hS]; simp)
    · exact Ideal.subset_span (by rw [hS]; simp)
    · exact Ideal.subset_span (by rw [hS]; simp)

theorem absNorm_p2 (hn : n % 8 = 5) : Ideal.absNorm (p2Ideal5 n) = 2 := by
  have h := congrArg Ideal.absNorm (p2_sq hn)
  rw [map_mul, Ideal.absNorm_span_singleton] at h
  have h2 : (Algebra.norm ℤ (2 : 𝓞 (QNeg n))).natAbs = 4 := by
    have := normZ_natCast (n := n) 2
    simp only [Nat.cast_ofNat] at this
    rw [this]; norm_num
  rw [h2] at h
  have : Ideal.absNorm (p2Ideal5 n) * Ideal.absNorm (p2Ideal5 n) = 2 * 2 := h
  nlinarith [Nat.zero_le (Ideal.absNorm (p2Ideal5 n))]

theorem a_mul_p2 (hn : n % 8 = 5) : varpiIdeal n * p2Ideal5 n = Ideal.span {sqrtNeg n - 1} := by
  rw [varpiIdeal, p2Ideal5, Ideal.span_pair_mul_span_pair]
  have hv := varpi_sq_add n
  have hm : (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) * 2 = (n : 𝓞 (QNeg n)) + 1 := by
    have : (n + 1) / 2 * 2 = n + 1 := by omega
    exact_mod_cast this
  apply le_antisymm
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rw [SetLike.mem_coe, Ideal.mem_span_singleton']
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨-(sqrtNeg n - 1) - 2, by linear_combination -hv - hm⟩
    · exact ⟨(((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)), by ring⟩
    · exact ⟨2, by ring⟩
    · exact ⟨sqrtNeg n - 1, rfl⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    set S : Set (𝓞 (QNeg n)) := {(((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) * 2,
      (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) * (sqrtNeg n - 1), (sqrtNeg n - 1) * 2,
      (sqrtNeg n - 1) * (sqrtNeg n - 1)} with hS
    have e : sqrtNeg n - 1 = 1 * ((((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) * (sqrtNeg n - 1)) -
        (((n + 1) / 4 : ℕ) : 𝓞 (QNeg n)) * ((sqrtNeg n - 1) * 2) := by
      have : (n + 1) / 2 = 2 * ((n + 1) / 4) + 1 := by omega
      have h' : (((n + 1) / 2 : ℕ) : 𝓞 (QNeg n)) = 2 * (((n + 1) / 4 : ℕ) : 𝓞 (QNeg n)) + 1 := by
        exact_mod_cast this
      rw [h']; ring
    rw [e]
    refine Ideal.sub_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
    · exact Ideal.subset_span (by rw [hS]; simp)
    · exact Ideal.subset_span (by rw [hS]; simp)


omit [NeZero n] in
theorem odd_of_mem_primeFactors (hodd : Odd n) {q : ℕ} (hq : q ∈ n.primeFactors) : q % 2 = 1 := by
  have hqd := Nat.dvd_of_mem_primeFactors hq
  have hqp := Nat.prime_of_mem_primeFactors hq
  rcases hqp.eq_two_or_odd with h | h
  · subst h; exact absurd (even_iff_two_dvd.2 hqd) (Nat.not_even_iff_odd.2 hodd)
  · exact h

omit [NeZero n] in
/-- `Π_{q ∣ n} (2/q) = (2/n) = −1` for squarefree `n ≡ 5 (mod 8)`. -/
theorem prod_sign_two (hn : n % 8 = 5) (hsq : Squarefree n) :
    ∏ q ∈ n.primeFactors, (if q % 8 = 1 ∨ q % 8 = 7 then (1 : ℤ) else -1) = -1 := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have h1 : ∀ q ∈ n.primeFactors, (if q % 8 = 1 ∨ q % 8 = 7 then (1 : ℤ) else -1) =
      ZMod.χ₈ (q : ZMod 8) := by
    intro q hq
    have hq2 := odd_of_mem_primeFactors hodd hq
    rw [ZMod.χ₈_nat_eq_if_mod_eight, if_neg (show ¬ (q % 2 = 0) by omega)]
  rw [Finset.prod_congr rfl h1, ← map_prod, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq,
    ZMod.χ₈_nat_eq_if_mod_eight, if_neg (show ¬ (n % 2 = 0) by omega),
    if_neg (show ¬ (n % 8 = 1 ∨ n % 8 = 7) by omega)]

omit [NeZero n] in
/-- `Π_{q ∣ n} q* = n` for squarefree `n ≡ 1 (mod 4)`. -/
theorem prod_pstar (hn : n % 4 = 1) (hsq : Squarefree n) :
    ∏ q ∈ n.primeFactors, pstar q = n := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have h1 : ∀ q ∈ n.primeFactors, pstar q = ZMod.χ₄ (q : ZMod 4) * (q : ℤ) := by
    intro q hq
    have hq2 := odd_of_mem_primeFactors hodd hq
    rw [ZMod.χ₄_nat_eq_if_mod_four, if_neg (show ¬ (q % 2 = 0) by omega)]
    unfold pstar
    split_ifs <;> ring
  rw [Finset.prod_congr rfl h1, Finset.prod_mul_distrib, ← map_prod, ← Nat.cast_prod, ← Nat.cast_prod,
    Nat.prod_primeFactors_of_squarefree hsq, ZMod.χ₄_nat_eq_if_mod_four,
    if_neg (show ¬ (n % 2 = 0) by omega), if_pos hn, one_mul]

theorem picToMax_picClass {K : Type} [Field K] [NumberField K] (O : NumberFieldOrder K)
    (J : integralIdealsPrimeTo O.conductorModulus) (hJ : (J : Ideal (𝓞 K)) ∈ (Ideal (𝓞 K))⁰) :
    picToMax O (O.picClass J) = (ClassGroup.mk0 ⟨(J : Ideal (𝓞 K)), hJ⟩ : ClassGroup (𝓞 K)) := by
  obtain ⟨t, ht⟩ := rayClassQuotient_surjective O.conductorModulus
    (idealClass O.conductorModulus J)
  have hQ : ringClassIdeleQuotient O t = O.picClass J := by
    rw [ringClassIdeleQuotient_apply, ht, rayClassToPic_idealClass]
  rw [← hQ, picToMax_ringClassIdeleQuotient, ringClassIdeleQuotient_apply,
    ← classMap_rayClassQuotient (maximal_conductorModulus_dvd O), ht, classMap_idealClass,
    rayClassToPic_idealClass]
  have hJ' : ((integralIdealsPrimeToInclusion (maximal_conductorModulus_dvd O) J :
      integralIdealsPrimeTo (maximalNumberFieldOrder K).conductorModulus) : Ideal (𝓞 K)) ∈
      (Ideal (𝓞 K))⁰ := by
    rw [coe_integralIdealsPrimeToInclusion]; exact hJ
  rw [picClass_maximal _ hJ']
  congr 2

theorem span_two_ne_zero (x : 𝓞 (QNeg n)) : Ideal.span {2, x} ≠ 0 := by
  intro h0
  have h2 : (2 : 𝓞 (QNeg n)) ∈ Ideal.span {2, x} := Ideal.subset_span (by simp)
  rw [h0, Ideal.zero_eq_bot, Ideal.mem_bot] at h2
  exact two_ne_zero h2

theorem chi_wClass (hn : n % 8 = 5) (hsq : Squarefree n) (q : n.primeFactors) :
    chi n q (picToMax (O4 n) (wClass n)) = Multiplicative.ofAdd (ZInQ.RouteK.legBit q 2) := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hq2 : (q : ℕ) % 2 = 1 := odd_of_mem_primeFactors hodd q.2
  have ha0 : varpiIdeal n ∈ (Ideal (𝓞 (QNeg n)))⁰ := mem_nonZeroDivisors_of_ne_zero (by
    rw [Ideal.zero_eq_bot]
    exact ((mem_integralIdealsPrimeTo_conductorModulus_iff (O4 n)).1 (varpiIdeal_mem hn)).1)
  have hp0 : p2Ideal5 n ∈ (Ideal (𝓞 (QNeg n)))⁰ :=
    mem_nonZeroDivisors_of_ne_zero (span_two_ne_zero _)
  rw [wClass_eq hn, picToMax_picClass (O4 n) ⟨_, varpiIdeal_mem hn⟩ ha0]
  have hprod : ClassGroup.mk0 (⟨varpiIdeal n, ha0⟩ : (Ideal (𝓞 (QNeg n)))⁰) *
      ClassGroup.mk0 (⟨p2Ideal5 n, hp0⟩ : (Ideal (𝓞 (QNeg n)))⁰) = 1 := by
    rw [← map_mul]
    have h2 : (⟨varpiIdeal n, ha0⟩ : (Ideal (𝓞 (QNeg n)))⁰) * ⟨p2Ideal5 n, hp0⟩ =
        ⟨Ideal.span {sqrtNeg n - 1}, by rw [← a_mul_p2 hn]; exact Submonoid.mul_mem _ ha0 hp0⟩ :=
      Subtype.ext (a_mul_p2 hn)
    rw [h2, ClassGroup.mk0_eq_one_iff]
    exact ⟨⟨sqrtNeg n - 1, rfl⟩⟩
  have hq : ¬ (q : ℕ) ∣ Ideal.absNorm (p2Ideal5 n) := by
    rw [absNorm_p2 hn]
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    have hqp := Nat.prime_of_mem_primeFactors q.2
    have := hqp.two_le
    omega
  have h3 := congrArg (chi n q) hprod
  rw [map_mul, map_one, chi_mk0 n hodd hsq q ⟨p2Ideal5 n, hp0⟩ hq, ← eq_inv_iff_mul_eq_one] at h3
  rw [h3, ← ofAdd_neg, ZMod.neg_eq_self_mod_two, absNorm_p2 hn, Nat.cast_ofNat]

theorem chi_wClass_eq_one_iff (hn : n % 8 = 5) (hsq : Squarefree n) (q : n.primeFactors) :
    chi n q (picToMax (O4 n) (wClass n)) = 1 ↔ (q : ℕ) % 8 = 1 ∨ (q : ℕ) % 8 = 7 := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hq2 : (q : ℕ) % 2 = 1 := odd_of_mem_primeFactors hodd q.2
  have hqp := Nat.prime_of_mem_primeFactors q.2
  haveI := Fact.mk hqp
  rw [chi_wClass hn hsq q, ← ZMod.exists_sq_eq_two_iff (by omega)]
  unfold ZInQ.RouteK.legBit
  rw [show (((2 : ℤ)) : ZMod q) = 2 by norm_num]
  split_ifs with h
  · simp [h]
  · simp only [h, iff_false]; decide

theorem sqrt_pstar_mem (hn4 : n % 4 = 1) (hsq : Squarefree n) (q : n.primeFactors) :
    sqrtK (QNeg n) (pstar q) ∈ hilbertField n := by
  have hi := adjSqrt_le_hilbertField hn4 hsq (-1) (Or.inl rfl)
    (IntermediateField.mem_adjoin_simple_self _ _)
  have hp := adjSqrt_le_hilbertField hn4 hsq (q : ℕ)
    (Or.inr ⟨q, Nat.prime_of_mem_primeFactors q.2, Nat.dvd_of_mem_primeFactors q.2, rfl⟩)
    (IntermediateField.mem_adjoin_simple_self _ _)
  unfold pstar
  split_ifs with h
  · exact hp
  · have e : (sqrtK (QNeg n) (-((q : ℕ) : ℤ))) ^ 2 =
        (sqrtK (QNeg n) (-1) * sqrtK (QNeg n) ((q : ℕ) : ℤ)) ^ 2 := by
      rw [mul_pow, sqrtK_sq, sqrtK_sq, sqrtK_sq]; push_cast; ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 e with h' | h'
    · rw [h']; exact mul_mem hi hp
    · rw [h']; exact neg_mem (mul_mem hi hp)

theorem acts_sqrt_pstar (hn4 : n % 4 = 1) (hsq : Squarefree n) {ρ : GalQ} {c : Pic (OK n)}
    (hρ : ActsAsArtinO n (OK n) ρ c) (q : n.primeFactors) :
    ρ (embed n (sqrtK (QNeg n) (pstar q))) =
      (if chi n q c = 1 then 1 else -1) * embed n (sqrtK (QNeg n) (pstar q)) := by
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hs := sqrt_pstar_mem hn4 hsq q
  have h1 := hρ ⟨_, hs⟩
  rw [h1, artinPstarChi_odd hodd hsq q c hs, map_mul]
  split_ifs <;> simp

/-- **Glue W-I proved**: `σ_w(i) = −i`. -/
theorem wNegatesI : WNegatesI := by
  intro n _ hn hsq ρ hρ
  have hn4 : n % 4 = 1 := by omega
  have hO := actsO_of_acts4 hρ
  set f : ℕ → Qbar := fun q => embed n (sqrtK (QNeg n) (pstar q)) with hf
  set s := ∏ q ∈ n.primeFactors, f q with hsdef
  have hsign : ∀ q ∈ n.primeFactors,
      ρ (f q) = (((if q % 8 = 1 ∨ q % 8 = 7 then (1 : ℤ) else -1 : ℤ)) : Qbar) * f q := by
    intro q hq
    have h1 := acts_sqrt_pstar hn4 hsq hO ⟨q, hq⟩
    simp only [hf]
    rw [h1]
    congr 1
    by_cases hc : q % 8 = 1 ∨ q % 8 = 7
    · rw [if_pos ((chi_wClass_eq_one_iff hn hsq ⟨q, hq⟩).2 hc), if_pos hc]; simp
    · rw [if_neg (fun h => hc ((chi_wClass_eq_one_iff hn hsq ⟨q, hq⟩).1 h)), if_neg hc]; simp
  have hρs : ρ s = -s := by
    rw [hsdef, map_prod, Finset.prod_congr rfl hsign, Finset.prod_mul_distrib, ← Int.cast_prod,
      prod_sign_two hn hsq]
    simp
  have hs2 : s ^ 2 = (n : Qbar) := by
    rw [hsdef, ← Finset.prod_pow]
    rw [Finset.prod_congr rfl (fun q _ => show f q ^ 2 = ((pstar q : ℤ) : Qbar) by
      simp only [hf]; rw [← map_pow, sqrtK_sq, map_intCast])]
    rw [← Int.cast_prod, prod_pstar hn4 hsq]
    simp
  have hω : ρ (omegaBar n) = omegaBar n := by
    have h1 := hρ ⟨algebraMap (QNeg n) (SeparableClosure (QNeg n)) QuadraticAlgebra.omega,
      (H4 n).algebraMap_mem _⟩
    simp only [omegaBar]
    rw [h1]
    congr 1
    exact congrArg Subtype.val ((artin4 n (wClass n)).commutes QuadraticAlgebra.omega)
  have hiQs : (iQ * s) ^ 2 = (omegaBar n) ^ 2 := by
    rw [mul_pow, iQ_sq, hs2, omegaBar_sq]; ring
  have hfix : ρ (iQ * s) = iQ * s := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hiQs with h | h
    · rw [h, hω]
    · rw [h, map_neg, hω]
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0] at hs2
    have : (n : Qbar) = 0 := by rw [← hs2]; ring
    exact NeZero.ne n (by exact_mod_cast this)
  rw [map_mul, hρs] at hfix
  have h' : (ρ iQ + iQ) * s = 0 := by linear_combination -hfix
  rcases mul_eq_zero.1 h' with h | h
  · linear_combination h
  · exact absurd h hs0

theorem mult_zmod2_eq_of_iff : ∀ x y : Multiplicative (ZMod 2), (x = 1 ↔ y = 1) → x = y := by
  decide

/-- **Glue BETA-5 proved**: `[σγ⁻¹] ≡ w` modulo `Cl(K_n)²`. -/
theorem betaOnGenus5 : BetaOnGenus5 := by
  intro n _ hn hsq σ γ hσ hγ a ha
  have hn4 : n % 4 = 1 := by omega
  have hodd : Odd n := Nat.odd_iff.mpr (by omega)
  have hO := actsO_of_acts4 ha
  rw [picSquares_eq_iInf_ker_chi n hodd hsq (by omega)]
  refine Subgroup.mem_iInf.2 fun q => ?_
  let φ : Pic (O4 n) →* Multiplicative (ZMod 2) := (chi n q).comp (picToMax (O4 n))
  show φ (a * (wClass n)⁻¹) = 1
  rw [map_mul, map_inv]
  suffices h : φ a = φ (wClass n) by rw [h, mul_inv_cancel]
  show chi n q (picToMax (O4 n) a) = chi n q (picToMax (O4 n) (wClass n))
  have hqp := Nat.prime_of_mem_primeFactors q.2
  have hq2 : (q : ℕ) % 2 = 1 := odd_of_mem_primeFactors hodd q.2
  set r := embed n (sqrtK (QNeg n) (pstar q)) with hr
  have hr2 : r ^ 2 = ((pstar q : ℤ) : Qbar) := by rw [hr, ← map_pow, sqrtK_sq, map_intCast]
  have hD : pstar q ≠ 0 := by
    unfold pstar; split_ifs <;> simp [hqp.ne_zero]
  have hr0 : r ≠ 0 := by
    intro h0; rw [h0] at hr2
    have : ((pstar q : ℤ) : Qbar) = 0 := by rw [← hr2]; ring
    exact hD (by exact_mod_cast this)
  have h1 := acts_sqrt_pstar hn4 hsq hO q
  have h2 : (σ * γ⁻¹) r = (if (q : ℕ) % 8 = 1 ∨ (q : ℕ) % 8 = 7 then 1 else -1) * r := by
    rw [AlgEquiv.mul_apply, hγ.inv_apply, hγ.apply_sqrt hD hr2, map_mul,
      hσ _ (squarefree_pstar hqp) r hr2, betaOneSign_pstar hqp (by omega)]
    push_cast
    split_ifs <;> simp [map_neg, map_one]
  rw [← hr] at h1
  have hne : (1 : Qbar) * r ≠ -1 * r := by
    intro h; apply hr0; linear_combination h / 2
  have hcmp : chi n q (picToMax (O4 n) a) = 1 ↔ ((q : ℕ) % 8 = 1 ∨ (q : ℕ) % 8 = 7) := by
    constructor
    · intro hc
      by_contra hc'
      rw [h1, if_pos hc, if_neg hc'] at h2
      exact hne h2
    · intro hc
      by_contra hc'
      rw [h1, if_neg hc', if_pos hc] at h2
      exact hne h2.symm
  exact mult_zmod2_eq_of_iff _ _ (hcmp.trans (chi_wClass_eq_one_iff hn hsq q).symm)

end Genus5

/-! ### `KerFixesZnMod`: the kernel of `Pic(O_{n,4}) → Cl(K_n)` is `{1, σ, w², σw²}`

A class in the kernel is `[(x) ∩ O]` with `x = u + v√−n ∈ 𝓞_K`, `u + v` odd (`odd_of_mem`: otherwise
`(x) + 𝔣 ⊆ 𝔭₂`). If `x ≡ a·y (mod 4𝓞_K)` with `a ∈ ℤ` then `[(x)] = [(y)]` (`picClass_congr`: `xȳ ∈ ℤ + 4𝓞_K`).
So the class is that of `1`, `1 + 2√−n` (`= σ`), `2 + √−n` (`= w²`, via `𝔞² = ((ω−1)²/2)`) or
`√−n ≡ (1+2√−n)(2+√−n)` (`= σw²`) (`ker_cases`). Then `σ` fixes `z_n` (tyz-cm) and `w²` moves it by
`τ((1+i)/2) + τ((1−i)/2) = τ(1)`. -/

section KerSec

open ZInQ.RouteK.Redei
open scoped nonZeroDivisors

variable {n : ℕ} [NeZero n]

/-! ### The kernel of `Pic(O_{n,4}) → Cl(K_n)` -/

section Ker

open QuadraticAlgebra

/-- `u + v√−n ∈ 𝓞_K`. -/
abbrev elt (n : ℕ) [NeZero n] (u v : ℤ) : 𝓞 (QNeg n) := (u : 𝓞 (QNeg n)) + (v : 𝓞 (QNeg n)) * sqrtNeg n

theorem coe_elt (u v : ℤ) : ((elt n u v : 𝓞 (QNeg n)) : QNeg n) = ⟨u, v⟩ := by
  simp only [elt]; push_cast [coe_sqrtNeg]; ext <;> simp

theorem eq_elt (hn4 : n % 4 = 1) (hsq : Squarefree n) (y : 𝓞 (QNeg n)) :
    ∃ u v : ℤ, y = elt n u v := by
  obtain ⟨u, v, hu, hv⟩ := Shimura.int_coords hn4 hsq y
  refine ⟨u, v, RingOfIntegers.ext ?_⟩
  rw [coe_elt]; ext <;> simp [hu, hv]

theorem elt_mul_conj (u v : ℤ) : elt n u v * elt n u (-v) = ((u ^ 2 + n * v ^ 2 : ℤ) : 𝓞 (QNeg n)) := by
  simp only [elt]; push_cast
  linear_combination (-(v : 𝓞 (QNeg n)) ^ 2) * sqrtNeg_mul_self (d := n)

theorem mem_O4_elt (a : ℤ) (z : 𝓞 (QNeg n)) : (a : 𝓞 (QNeg n)) + 4 * z ∈ (O4 n).toRingOfIntegers := by
  rw [NumberFieldOrder.mem_toRingOfIntegers, Shimura.mem_O4_iff']
  refine ⟨a, z, ?_⟩
  simp only [map_add, map_mul, map_intCast, map_ofNat]

theorem odd_norm {n : ℕ} (hn : n % 2 = 1) {u v : ℤ} (huv : (u + v) % 2 = 1) :
    ∃ M : ℤ, u ^ 2 + n * v ^ 2 = 2 * M + 1 := by
  rcases Int.emod_two_eq_zero_or_one u with hu | hu
  · obtain ⟨a, rfl⟩ : ∃ a, u = 2 * a := ⟨u / 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, v = 2 * b + 1 := ⟨v / 2, by omega⟩
    obtain ⟨c, hc⟩ : ∃ c, (n : ℤ) = 2 * c + 1 := ⟨n / 2, by omega⟩
    exact ⟨2 * a ^ 2 + (2 * c + 1) * (2 * b ^ 2 + 2 * b) + c, by rw [hc]; ring⟩
  · obtain ⟨a, rfl⟩ : ∃ a, u = 2 * a + 1 := ⟨u / 2, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, v = 2 * b := ⟨v / 2, by omega⟩
    exact ⟨2 * a ^ 2 + 2 * a + 2 * n * b ^ 2, by ring⟩

/-- `(u + v√−n)` with `u + v` odd is prime to the conductor of `O_{n,4}`. -/
theorem span_elt_mem (hn : n % 8 = 5) {u v : ℤ} (huv : (u + v) % 2 = 1) :
    Ideal.span {elt n u v} ∈ integralIdealsPrimeTo (O4 n).conductorModulus := by
  rw [mem_integralIdealsPrimeTo_conductorModulus_iff]
  obtain ⟨M, hM⟩ := odd_norm (n := n) (by omega) huv
  have hN := elt_mul_conj (n := n) u v
  refine ⟨?_, ?_⟩
  · intro h
    have hx : elt n u v ∈ Ideal.span {elt n u v} := Ideal.subset_span rfl
    rw [h, Ideal.mem_bot] at hx
    rw [hx, zero_mul, hM] at hN
    have h1 : (((2 * M + 1 : ℤ)) : 𝓞 (QNeg n)) = ((0 : ℤ) : 𝓞 (QNeg n)) := by
      rw [← hN]; simp
    have := intCast_injective (n := n) h1
    omega
  · rw [Ideal.eq_top_iff_one]
    -- 1 = x * (x̄ * (2M+1)) - 4 * (M * (M + 1))
    have e : (1 : 𝓞 (QNeg n)) = elt n u v * (elt n u (-v) * ((2 * M + 1 : ℤ) : 𝓞 (QNeg n))) +
        4 * ((-(M * (M + 1)) : ℤ) : 𝓞 (QNeg n)) := by
      rw [← mul_assoc, hN, hM]; push_cast; ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)))
      (Ideal.mem_sup_right ?_)
    simpa using natCast_mul_mem_conductor (QNeg n) 4 (((-(M * (M + 1)) : ℤ)) : 𝓞 (QNeg n))

/-- **Congruence lemma**: if `x ≡ a·y (mod 4𝓞_K)`, `a ∈ ℤ`, then `[x ∩ O] = [y ∩ O]` in `Pic(O_{n,4})`. -/
theorem picClass_congr (hn : n % 8 = 5) {u v u' v' : ℤ} (huv : (u + v) % 2 = 1)
    (huv' : (u' + v') % 2 = 1) (a : ℤ) (z : 𝓞 (QNeg n))
    (h : elt n u v = a * elt n u' v' + 4 * z) :
    (O4 n).picClass ⟨_, span_elt_mem hn huv⟩ = (O4 n).picClass ⟨_, span_elt_mem hn huv'⟩ := by
  have huv'' : (u' + -v') % 2 = 1 := by omega
  have hb := span_elt_mem hn huv''
  have hN := elt_mul_conj (n := n) u' v'
  -- `[x][ȳ] = 1` and `[y][ȳ] = 1`
  have hprod : ∀ {x : 𝓞 (QNeg n)} (hx : Ideal.span {x} ∈ integralIdealsPrimeTo (O4 n).conductorModulus)
      (hxy : x * elt n u' (-v') ∈ (O4 n).toRingOfIntegers),
      (O4 n).picClass ⟨_, hx⟩ * (O4 n).picClass ⟨_, hb⟩ = 1 := by
    intro x hx hxy
    rw [← map_mul]
    have hm : (⟨_, hx⟩ : integralIdealsPrimeTo (O4 n).conductorModulus) * ⟨_, hb⟩ =
        ⟨Ideal.span {x * elt n u' (-v')}, by
          rw [← Ideal.span_singleton_mul_span_singleton]; exact Submonoid.mul_mem _ hx hb⟩ :=
      Subtype.ext (Ideal.span_singleton_mul_span_singleton _ _)
    rw [hm, picClass_eq_one_iff]
    exact ⟨_, hxy, rfl⟩
  have h1 := hprod (span_elt_mem hn huv) (by
    rw [h, add_mul, mul_assoc, hN, ← Int.cast_mul, mul_assoc]
    exact mem_O4_elt _ _)
  have h2 := hprod (span_elt_mem hn huv') (by
    rw [hN]
    have := mem_O4_elt (n := n) (u' ^ 2 + n * v' ^ 2) 0
    rwa [mul_zero, add_zero] at this)
  exact mul_right_cancel (h1.trans h2.symm)

end Ker

section Ker2
open QuadraticAlgebra

theorem elt_mem_p2 {u v : ℤ} (huv : (u + v) % 2 = 0) : elt n u v ∈ p2Ideal5 n := by
  obtain ⟨t, ht⟩ : ∃ t, u + v = 2 * t := ⟨(u + v) / 2, by omega⟩
  have e : elt n u v = (t : 𝓞 (QNeg n)) * 2 + (v : 𝓞 (QNeg n)) * (sqrtNeg n - 1) := by
    simp only [elt]
    have : (u : 𝓞 (QNeg n)) = 2 * t - v := by
      have h' : ((u : ℤ) : 𝓞 (QNeg n)) = ((2 * t - v : ℤ) : 𝓞 (QNeg n)) := by rw [← ht]; ring_nf
      push_cast at h'; exact h'
    rw [this]; ring
  rw [e, p2Ideal5]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

theorem conductor_le_p2 (hn : n % 8 = 5) (hsq : Squarefree n) : (O4 n).conductor ≤ p2Ideal5 n := by
  have hn4 : n % 4 = 1 := by omega
  intro c hc
  rw [NumberFieldOrder.mem_conductor_iff] at hc
  have h1 := hc 1
  have h2 := hc (sqrtNeg n)
  rw [Shimura.mem_O4_iff'] at h1 h2
  obtain ⟨a, y, hy⟩ := h1
  obtain ⟨a', y', hy'⟩ := h2
  obtain ⟨y1, y2, hy1, hy2⟩ := Shimura.int_coords hn4 hsq y
  obtain ⟨y1', y2', hy1', hy2'⟩ := Shimura.int_coords hn4 hsq y'
  rw [show ((1 : 𝓞 (QNeg n)) : QNeg n) = 1 from rfl, mul_one] at hy
  rw [hy, coe_sqrtNeg] at hy'
  have him := congrArg QuadraticAlgebra.im hy'
  simp [hy1, hy2, hy1', hy2'] at him
  have ha : (a : ℚ) = 4 * (y2' - y1) := by linarith
  have ha' : a = 4 * (y2' - y1) := by exact_mod_cast ha
  have e : c = 2 * (2 * (((y2' - y1 : ℤ) : 𝓞 (QNeg n)) + y)) := by
    apply RingOfIntegers.ext
    have hcI : ∀ m : ℤ, ((m : 𝓞 (QNeg n)) : QNeg n) = m := fun m =>
      map_intCast (algebraMap (𝓞 (QNeg n)) (QNeg n)) m
    rw [hy, ha']; push_cast [Shimura.coeO_two, hcI]; ring
  rw [e, p2Ideal5]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem p2_ne_top (hn : n % 8 = 5) : p2Ideal5 n ≠ ⊤ := by
  intro h
  have := absNorm_p2 (n := n) hn
  rw [h, Ideal.absNorm_top] at this
  omega

/-- A principal ideal `(u + v√−n)` prime to the conductor has `u + v` odd. -/
theorem odd_of_mem (hn : n % 8 = 5) (hsq : Squarefree n) {u v : ℤ}
    (h : Ideal.span {elt n u v} ∈ integralIdealsPrimeTo (O4 n).conductorModulus) :
    (u + v) % 2 = 1 := by
  by_contra hc
  have hc' : (u + v) % 2 = 0 := by omega
  rw [mem_integralIdealsPrimeTo_conductorModulus_iff] at h
  apply p2_ne_top hn
  rw [eq_top_iff, ← h.2]
  exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 (elt_mem_p2 hc')) (conductor_le_p2 hn hsq)

end Ker2

section Ker3
open QuadraticAlgebra

theorem elt_lin (a u' v' s t : ℤ) :
    (a : 𝓞 (QNeg n)) * elt n u' v' + 4 * elt n s t = elt n (a * u' + 4 * s) (a * v' + 4 * t) := by
  simp only [elt]; push_cast; ring

theorem elt_mul (u v u' v' : ℤ) :
    elt n u v * elt n u' v' = elt n (u * u' - n * v * v') (u * v' + v * u') := by
  simp only [elt]; push_cast
  linear_combination ((v : 𝓞 (QNeg n)) * v') * sqrtNeg_mul_self (d := n)

theorem pic_one (hn : n % 8 = 5) :
    (O4 n).picClass ⟨_, span_elt_mem (n := n) hn (u := 1) (v := 0) (by decide)⟩ = 1 := by
  rw [picClass_eq_one_iff]
  refine ⟨elt n 1 0, ?_, rfl⟩
  simpa [elt] using mem_O4_elt (n := n) 1 0

theorem pic_sigma (hn : n % 8 = 5) :
    (O4 n).picClass ⟨_, span_elt_mem (n := n) hn (u := 1) (v := 2) (by decide)⟩ = sigmaClass n := by
  rw [sigmaClass_eq]
  have e : alpha n = elt n 3 2 := by simp only [alpha, elt]; push_cast; ring
  have h1 : (O4 n).picClass ⟨_, alphaIdeal_mem⟩ =
      (O4 n).picClass ⟨_, span_elt_mem (n := n) hn (u := 3) (v := 2) (by decide)⟩ := by
    congr 1 <;> simp [e]
  rw [h1]
  exact (picClass_congr hn (u := 3) (v := 2) (u' := 1) (v' := 2) (by decide) (by decide) (-1)
    (elt n 1 1) (by rw [elt_lin]; norm_num)).symm

theorem varpi_sq (k : ℕ) (hk : n = 8 * k + 5) :
    (sqrtNeg n - 1) * (sqrtNeg n - 1) = 2 * elt n (-4 * k - 2) (-1) := by
  have hk' : (n : 𝓞 (QNeg n)) = 8 * (k : 𝓞 (QNeg n)) + 5 := by
    have := congrArg (Nat.cast (R := 𝓞 (QNeg n))) hk
    push_cast at this; exact this
  simp only [elt]; push_cast
  linear_combination sqrtNeg_mul_self (d := n) - hk'

theorem a_sq (hn : n % 8 = 5) (k : ℕ) (hk : n = 8 * k + 5) :
    varpiIdeal n * varpiIdeal n = Ideal.span {elt n (-4 * k - 2) (-1)} := by
  have h2 : (Ideal.span {(2 : 𝓞 (QNeg n))}) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact two_ne_zero
  apply mul_right_cancel₀ h2
  rw [← p2_sq hn]
  calc varpiIdeal n * varpiIdeal n * (p2Ideal5 n * p2Ideal5 n)
      = (varpiIdeal n * p2Ideal5 n) * (varpiIdeal n * p2Ideal5 n) := by ring
    _ = Ideal.span {(sqrtNeg n - 1) * (sqrtNeg n - 1)} := by
        rw [a_mul_p2 hn, Ideal.span_singleton_mul_span_singleton]
    _ = _ := by
        rw [varpi_sq k hk, ← Ideal.span_singleton_mul_span_singleton, mul_comm, p2_sq hn]

theorem pic_w2 (hn : n % 8 = 5) :
    (O4 n).picClass ⟨_, span_elt_mem (n := n) hn (u := 2) (v := 1) (by decide)⟩ = wClass n ^ 2 := by
  have hb : ((-4 * ((n / 8 : ℕ) : ℤ) - 2) + -1) % 2 = 1 := by omega
  have hk : n = 8 * (n / 8) + 5 := by omega
  rw [wClass_eq hn, ← map_pow]
  have h1 : (⟨_, varpiIdeal_mem hn⟩ : integralIdealsPrimeTo (O4 n).conductorModulus) ^ 2 =
      ⟨_, span_elt_mem hn hb⟩ := Subtype.ext (by
        show varpiIdeal n ^ 2 = _
        rw [pow_two, a_sq hn (n / 8) hk])
  rw [h1]
  exact (picClass_congr hn (u' := 2) (v' := 1) hb (by decide) (-1) (elt n (-((n / 8 : ℕ) : ℤ)) 0)
    (by rw [elt_lin]; congr 1 <;> ring)).symm

theorem pic_omega (hn : n % 8 = 5) :
    (O4 n).picClass ⟨_, span_elt_mem (n := n) hn (u := 0) (v := 1) (by decide)⟩ =
      sigmaClass n * wClass n ^ 2 := by
  have hb : ((1 * 2 - (n : ℤ) * 2 * 1) + (1 * 1 + 2 * 2)) % 2 = 1 := by omega
  rw [← pic_sigma hn, ← pic_w2 hn, ← map_mul]
  have h1 : (⟨_, span_elt_mem (n := n) hn (u := 1) (v := 2) (by decide)⟩ :
      integralIdealsPrimeTo (O4 n).conductorModulus) *
        ⟨_, span_elt_mem (n := n) hn (u := 2) (v := 1) (by decide)⟩ =
      ⟨_, span_elt_mem hn hb⟩ := Subtype.ext (by
        show Ideal.span _ * Ideal.span _ = _
        rw [Ideal.span_singleton_mul_span_singleton, elt_mul])
  rw [h1]
  exact (picClass_congr hn (u' := 0) (v' := 1) hb (by decide) 1 (elt n (-4 * (n / 8 : ℕ) - 2) 1)
    (by rw [elt_lin]; congr 1 <;> omega)).symm

/-- **The kernel of `Pic(O_{n,4}) → Cl(K_n)` is `{1, σ, w², σw²}`** (for `n ≡ 5 (mod 8)`). -/
theorem ker_cases (hn : n % 8 = 5) (hsq : Squarefree n) {k : Pic (O4 n)}
    (hk : picToMax (O4 n) k = 1) :
    k = 1 ∨ k = sigmaClass n ∨ k = wClass n ^ 2 ∨ k = sigmaClass n * wClass n ^ 2 := by
  have hn4 : n % 4 = 1 := by omega
  obtain ⟨J, rfl⟩ := (O4 n).picClass_surjective k
  have hJ0 : (J : Ideal (𝓞 (QNeg n))) ∈ (Ideal (𝓞 (QNeg n)))⁰ := mem_nonZeroDivisors_of_ne_zero (by
    rw [Ideal.zero_eq_bot]
    exact ((mem_integralIdealsPrimeTo_conductorModulus_iff (O4 n)).1 J.2).1)
  rw [picToMax_picClass (O4 n) J hJ0] at hk
  have hk' : (ClassGroup.mk0 ⟨(J : Ideal (𝓞 (QNeg n))), hJ0⟩ : ClassGroup (𝓞 (QNeg n))) = 1 := hk
  rw [ClassGroup.mk0_eq_one_iff] at hk'
  obtain ⟨⟨x, hx⟩⟩ := hk'
  obtain ⟨u, v, rfl⟩ := eq_elt hn4 hsq x
  have hmem : Ideal.span {elt n u v} ∈ integralIdealsPrimeTo (O4 n).conductorModulus := by
    have := J.2; rw [show (J : Ideal (𝓞 (QNeg n))) = Ideal.span {elt n u v} from hx] at this
    exact this
  have huv := odd_of_mem hn hsq hmem
  have hJ : J = ⟨_, span_elt_mem hn huv⟩ := Subtype.ext hx
  rw [hJ]
  rcases (by omega : v % 4 = 0 ∨ v % 4 = 2 ∨ (v % 2 = 1 ∧ u % 4 = 0) ∨ (v % 2 = 1 ∧ u % 4 = 2))
    with h | h | h | h
  · left
    rw [picClass_congr hn huv (u' := 1) (v' := 0) (by decide) u (elt n 0 (v / 4)) (by rw [elt_lin]; congr 1 <;> omega),
      pic_one hn]
  · right; left
    rw [picClass_congr hn huv (u' := 1) (v' := 2) (by decide) u (elt n 0 ((v - 2 * u) / 4))
      (by rw [elt_lin]; congr 1 <;> omega), pic_sigma hn]
  · right; right; right
    rw [picClass_congr hn huv (u' := 0) (v' := 1) (by decide) v (elt n (u / 4) 0) (by rw [elt_lin]; congr 1 <;> omega),
      pic_omega hn]
  · right; right; left
    rw [picClass_congr hn huv (u' := 2) (v' := 1) (by decide) v (elt n ((u - 2 * v) / 4) 0)
      (by rw [elt_lin]; congr 1 <;> omega), pic_w2 hn]

end Ker3

end KerSec

section KerFix

theorem acts4_one (n : ℕ) [NeZero n] : ActsAsArtin4 1 n 1 := by
  intro x; simp

/-- **Glue KER proved.** -/
theorem kerFixesZnMod (hs : TYZSigmaFixesZn) (hw : TYZThm36OneFive) (hz : ZnOverH4) :
    KerFixesZnMod := by
  intro n hn0 hn hsq k hk ρ hρ
  have hzH := hz n hn hsq
  let P : Pic (O4 n) → Prop := fun c => ∀ ρ : GalQ, ActsAsArtin4 ρ n c →
    ∃ j : ℤ, galPt ρ (tyzZn n) = tyzZn n + j • tauG 2
  have hmul : ∀ c c', P c → P c' → P (c * c') := by
    intro c c' hc hc' ρ hρ
    obtain ⟨ρ1, h1⟩ := exists_actsAsArtin4 n c
    obtain ⟨ρ2, h2⟩ := exists_actsAsArtin4 n c'
    obtain ⟨j1, hj1⟩ := hc ρ1 h1
    obtain ⟨j2, hj2⟩ := hc' ρ2 h2
    refine ⟨j1 + j2, ?_⟩
    rw [acts4_galPt hρ (acts4_mul h1 h2) hzH, galPt_mul, hj2, map_add, map_zsmul, galPt_tauG_two,
      hj1, add_zsmul]
    abel
  have h1 : P 1 := fun ρ hρ => ⟨0, by
    rw [acts4_galPt hρ (acts4_one n) hzH, galPt_one, zero_zsmul, add_zero]⟩
  have hσ : P (sigmaClass n) := fun ρ hρ => ⟨0, by
    rw [hs n hn0 hn hsq ρ hρ, zero_zsmul, add_zero]⟩
  have hw2 : P (wClass n ^ 2) := by
    intro ρ hρ
    obtain ⟨ρw, hρw⟩ := exists_actsAsArtin4 n (wClass n)
    obtain ⟨k1, hk1⟩ := hw n hn0 hn hsq ρw hρw
    have hi := wNegatesI n hn0 hn hsq ρw hρw
    refine ⟨1 + 2 * k1, ?_⟩
    rw [acts4_galPt hρ (by rw [pow_two]; exact acts4_mul hρw hρw) hzH, galPt_mul, hk1, map_add,
      map_add, hk1, map_zsmul, galPt_tauG_two, galPt_tauG_one_one_of_neg hi]
    have h11 := tauG_one_one_add
    rw [← h11]
    module
  rcases ker_cases hn hsq hk with rfl | rfl | rfl | rfl
  · exact h1 ρ hρ
  · exact hσ ρ hρ
  · exact hw2 ρ hρ
  · exact hmul _ _ hσ hw2 ρ hρ

end KerFix

/-! ### The main glue: `Lemma321Five` from the inputs -/

section Main

theorem betaOneSign_neg_five {e : ℕ} (he : e % 8 = 5) : betaOneSign (-(e : ℤ)) = -1 := by
  have h2 : ¬ (2 : ℤ) ∣ -(e : ℤ) := by omega
  have h8 : (-(e : ℤ)) % 8 = 3 := by omega
  have he0 : e ≠ 0 := by omega
  simp [betaOneSign, oddPartSqfree, h2, h8, he0]

theorem fixes_omegaBar {e : ℕ} [NeZero e] (he : e % 8 = 5) (hse : Squarefree e) {σ γ : GalQ}
    (hσ : IsBetaOneLift σ) (hγ : IsComplexConj γ) : (σ * γ⁻¹) (omegaBar e) = omegaBar e := by
  have hsq : omegaBar e ^ 2 = ((-(e : ℤ) : ℤ) : Qbar) := by rw [omegaBar_sq]; push_cast; ring
  have hD : (-(e : ℤ)) ≠ 0 := by omega
  have hγω : γ (omegaBar e) = -omegaBar e := by
    rw [hγ.apply_sqrt hD hsq, if_pos (by omega)]; ring
  have hsqf : Squarefree (-(e : ℤ)) := sqf_neg (Int.squarefree_natCast.2 hse)
  have hσω : σ (omegaBar e) = -omegaBar e := by
    rw [hσ _ hsqf _ hsq, betaOneSign_neg_five he]; push_cast; ring
  rw [AlgEquiv.mul_apply, hγ.inv_apply, hγω, map_neg, hσω, neg_neg]

/-- `z_n ∈ A(H_{n,4})` from `Shimura.ShimuraReciprocityModFn`. -/
theorem znOverH4_of (hS : Shimura.ShimuraReciprocityModFn) : ZnOverH4 := by
  intro n hn hsq
  have h1 := cmFieldTYZ_of_ringClassD (Shimura.cmFieldOfDefinition_of_shimuraModFn hS) n hn hsq
  have hi := iInH4 n hn hsq
  exact sub_mem h1 (iPt_mem hi h1)

/-- **The core glue**: TYZ's proof of Lemma 3.21(1) for one `e ≡ 5 (mod 8)` and any lift `σ`. -/
theorem five_single (hz : ZnOverH4) (hc : TYZThm36ConjFive) (hw : TYZThm36OneFive)
    (hk : KerFixesZnMod) (hg : BetaOnGenus5) {e : ℕ} [NeZero e] (he5 : e % 8 = 5)
    (hse : Squarefree e) {σ : GalQ} (hσ : IsBetaOneLift σ) :
    ∃ k : ℤ, galPt σ (genusSum (Phi0 e) (tyzZn e)) + genusSum (Phi0 e) (tyzZn e) =
      (gNat e : ℤ) • tauG ⟨1, -1⟩ + k • tauG 2 := by
  classical
  obtain ⟨γ, hγ⟩ := exists_complexConj
  obtain ⟨a, ha⟩ := exists_acts4_of_fix (fixes_omegaBar he5 hse hσ hγ)
  have hzH : (tyzZn e) ∈ ptsOver (H4bar e) := hz e he5 hse
  have hb := hg e inferInstance he5 hse σ γ hσ hγ a ha
  set T := Phi0 e with hTdef
  have hT : IsPhi0 e T := phi0_spec e
  set P := picToMax (O4 e) with hPdef
  set w := wClass e with hwdef
  have hcl : ∀ t ∈ T, ∃ c ∈ picSquares (O4 e), ActsAsArtin4 t e c := hT.1
  choose! cl hclsq hclact using hcl
  have hPsq : ∀ t ∈ T, P (cl t) ∈ picSquares (OK e) := by
    intro t ht
    obtain ⟨b, hb'⟩ := hclsq t ht
    exact ⟨P b, by rw [← hb']; simp [powMonoidHom_apply, map_pow]⟩
  have huniq : ∀ c' ∈ picSquares (OK e), ∀ ρ₁ ∈ T, ∀ ρ₂ ∈ T, ActsAsArtinO e (OK e) ρ₁ c' →
      ActsAsArtinO e (OK e) ρ₂ c' → ρ₁ = ρ₂ := by
    intro c' hc' ρ₁ h₁ ρ₂ h₂ a₁ a₂
    exact (hT.2 c' hc').unique ⟨h₁, a₁⟩ ⟨h₂, a₂⟩
  have hactsO : ∀ t ∈ T, ActsAsArtinO e (OK e) t (P (cl t)) := fun t ht =>
    actsO_of_acts4 (hclact t ht)
  have hinj : ∀ t₁ ∈ T, ∀ t₂ ∈ T, P (cl t₁) = P (cl t₂) → t₁ = t₂ := by
    intro t₁ h₁ t₂ h₂ hP
    exact huniq _ (hPsq t₂ h₂) t₁ h₁ t₂ h₂ (hP ▸ hactsO t₁ h₁) (hactsO t₂ h₂)
  set B := P (a * w⁻¹) with hBdef
  have htgt : ∀ t ∈ T, B * (P (cl t))⁻¹ ∈ picSquares (OK e) := fun t ht =>
    Subgroup.mul_mem _ hb (Subgroup.inv_mem _ (hPsq t ht))
  have hex : ∀ t ∈ T, ∃ s, s ∈ T ∧ ActsAsArtinO e (OK e) s (B * (P (cl t))⁻¹) :=
    fun t ht => (hT.2 _ (htgt t ht)).exists
  choose! f hfT hfact using hex
  have hPf : ∀ t ∈ T, P (cl (f t)) = B * (P (cl t))⁻¹ := fun t ht =>
    artinO_inj e (hactsO (f t) (hfT t ht)) (hfact t ht)
  have hτ2 : ∀ ρ : GalQ, galPt ρ (tauG 2) = tauG 2 := galPt_tauG_two
  have key : ∀ t ∈ T, ∃ j : ℤ,
      galPt σ (galPt t (tyzZn e)) = tauG ⟨1, -1⟩ - galPt (f t) (tyzZn e) + j • tauG 2 := by
    intro t ht
    obtain ⟨ρw, hρw⟩ := exists_actsAsArtin4 e w
    set k := a * (cl t)⁻¹ * w⁻¹ * (cl (f t))⁻¹ with hkdef
    have hk1 : P k = 1 := by
      rw [hkdef, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, hPf t ht, hBdef, map_mul,
        map_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel
    obtain ⟨ρk, hρk⟩ := exists_actsAsArtin4 e k
    have h1 : σ * t = (σ * γ⁻¹) * (γ * t * γ⁻¹) * γ := by group
    have hA : ActsAsArtin4 ((σ * γ⁻¹) * (γ * t * γ⁻¹)) e (a * (cl t)⁻¹) :=
      acts4_mul ha (actsAsArtin4_conj (hγ.ne_omega e) (hclact t ht))
    have hB : ActsAsArtin4 (f t * ρk * ρw) e (a * (cl t)⁻¹) := by
      have := acts4_mul (acts4_mul (hclact (f t) (hfT t ht)) hρk) hρw
      convert this using 1
      rw [hkdef]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    obtain ⟨k1, hk1'⟩ := hw e inferInstance he5 hse ρw hρw
    obtain ⟨j2, hj2⟩ := hk e inferInstance he5 hse k hk1 ρk hρk
    obtain ⟨j3, hj3⟩ := galPt_tauG_one_one ρk
    have hfi : (f t) iQ = iQ := by
      obtain ⟨b, hb2⟩ := hclsq (f t) (hfT t ht)
      have hact := hclact (f t) (hfT t ht)
      rw [← hb2] at hact
      exact fixes_iQ_of_actsAsArtin4_sq hact
    refine ⟨-(k1 + j2 + j3), ?_⟩
    rw [← galPt_mul, h1, galPt_mul (σ * γ⁻¹ * (γ * t * γ⁻¹)) γ, hc e he5 hse γ hγ, map_sub, hτ2,
      acts4_galPt hA hB hzH, galPt_mul, galPt_mul, hk1']
    simp only [map_add, map_zsmul, hj2, hj3, hτ2, galPt_tauG _ hfi]
    have h11 : tauG ⟨1, 1⟩ = tauG 2 - tauG ⟨1, -1⟩ := eq_sub_of_add_eq tauG_one_one_add
    rw [h11]
    module
  choose! J hJ using key
  have hsum : ∑ t ∈ T, galPt (f t) (tyzZn e) = ∑ t ∈ T, galPt t (tyzZn e) := by
    refine Finset.sum_nbij f hfT ?_ ?_ (fun t _ => rfl)
    · intro t₁ h₁ t₂ h₂ he
      have h := (hPf t₁ h₁).symm.trans ((congrArg (fun s => P (cl s)) he).trans (hPf t₂ h₂))
      exact hinj t₁ h₁ t₂ h₂ (inv_injective (mul_left_cancel h))
    · intro s hs
      obtain ⟨t, ⟨htT, htact⟩, -⟩ := hT.2 (B * (P (cl s))⁻¹) (htgt s hs)
      refine ⟨t, htT, ?_⟩
      have hPt : P (cl t) = B * (P (cl s))⁻¹ := artinO_inj e (hactsO t htT) htact
      have : P (cl (f t)) = P (cl s) := by
        rw [hPf t htT, hPt]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      exact hinj _ (hfT t htT) s hs this
  have hcard : T.card = gNat e := by
    rw [← card_sqClasses]
    refine Finset.card_nbij (fun t => P (cl t)) (fun t ht => mem_sqClasses.2 (hPsq t ht)) ?_ ?_
    · intro t₁ h₁ t₂ h₂ he; exact hinj t₁ h₁ t₂ h₂ he
    · intro c' hc'
      rw [Finset.mem_coe, mem_sqClasses] at hc'
      obtain ⟨t, ⟨htT, htact⟩, -⟩ := hT.2 c' hc'
      exact ⟨t, htT, artinO_inj e (hactsO t htT) htact⟩
  refine ⟨∑ t ∈ T, J t, ?_⟩
  simp only [genusSum, map_sum]
  rw [← Finset.sum_add_distrib, Finset.sum_congr rfl (fun t ht => by rw [hJ t ht])]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, hsum, hcard,
    ← Finset.sum_smul]
  rw [natCast_zsmul]
  abel

/-- **`Lemma321Five` from the inputs** (any lift `σ` works for every `e`). -/
theorem lemma321Five_of (hβ : BetaOneLiftExists) (hz : ZnOverH4) (hc : TYZThm36ConjFive)
    (hw : TYZThm36OneFive) (hk : KerFixesZnMod) (hg : BetaOnGenus5) : Lemma321Five := by
  intro n hn hsq
  obtain ⟨σ, hσ⟩ := hβ
  refine ⟨σ, hσ, fun e he he5 => ?_⟩
  have hse : Squarefree e := hsq.squarefree_of_dvd (Nat.dvd_of_mem_divisors he)
  haveI : NeZero e := ⟨by omega⟩
  rw [tyzZ_five he5]
  exact five_single hz hc hw hk hg he5 hse hσ

/-- **`Lemma321Five` from tyz-cm's textbook CM leaf, `BetaOneLiftExists` and `KerFixesZnMod`.** -/
theorem lemma321Five_of_shimuraModFn (hS : Shimura.ShimuraReciprocityModFn)
    (hβ : BetaOneLiftExists) (hk : KerFixesZnMod) : Lemma321Five :=
  lemma321Five_of hβ (znOverH4_of hS)
    (tyzThm36ConjFive_of (cmAlgebraic_of_cmValue (Shimura.cmValueRingClass_of_modFn hS)))
    (tyzThm36OneFive_of (Shimura.shimuraReciprocityPic_of_shimuraModFn hS)
      (cmAlgebraic_of_cmValue (Shimura.cmValueRingClass_of_modFn hS)) wNegatesI)
    hk betaOnGenus5

/-- **`Lemma321Five` from tyz-cm's textbook CM leaf and `BetaOneLiftExists`.** -/
theorem lemma321Five_of_shimuraModFn_betaOneLift (hS : Shimura.ShimuraReciprocityModFn)
    (hβ : BetaOneLiftExists) : Lemma321Five :=
  lemma321Five_of_shimuraModFn hS hβ
    (kerFixesZnMod
      (Shimura.tyzSigmaFixesZn_of (Shimura.shimuraReciprocityPic_of_shimuraModFn hS)
        Shimura.etaModelFricke)
      (tyzThm36OneFive_of (Shimura.shimuraReciprocityPic_of_shimuraModFn hS)
        (cmAlgebraic_of_cmValue (Shimura.cmValueRingClass_of_modFn hS)) wNegatesI)
      (znOverH4_of hS))

open ZInQ.Contrib.TYZDecomp in
/-- **TYZ reading A with `Lemma321Five` discharged**: from the three `𝓛`-leaves, tyz-cm's textbook CM
leaf `Shimura.ShimuraReciprocityModFn`, TYZ Lemma `torsion2` (`Lemma318Literal`), Theorem 3.3/3.5
(`Thm35First`) and the glue `BetaOneLiftExists` (Kummer theory over `ℚ`). -/
theorem tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First_betaOneLift
    (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hS : Shimura.ShimuraReciprocityModFn)
    (h318 : Lemma318Literal HHprime) (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ)
    (hβ : BetaOneLiftExists) : ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First_lemma321Five h11 h1 h29 hS h318 h35
    (lemma321Five_of_shimuraModFn_betaOneLift hS hβ)

/-- **Glue BETA-EX proved** (`T321B.betaOneLiftExists`). -/
theorem betaOneLiftExists' : BetaOneLiftExists := ZInQ.Contrib.TYZGenus.T321B.betaOneLiftExists

/-- **`Lemma321Five` (TYZ Lemma 3.21(1), pinned) from tyz-cm's textbook CM leaf alone.** -/
theorem lemma321Five_of_shimuraModFn' (hS : Shimura.ShimuraReciprocityModFn) : Lemma321Five :=
  lemma321Five_of_shimuraModFn_betaOneLift hS betaOneLiftExists'

open ZInQ.Contrib.TYZDecomp in
/-- **TYZ reading A from the three `𝓛`-leaves, `Shimura.ShimuraReciprocityModFn`, TYZ Lemma `torsion2`
(`Lemma318Literal`) and Theorem 3.3/3.5 (`Thm35First`)**: cm-bridge's headline with `Lemma321Five`
removed. -/
theorem tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First
    (h11 : TYZThm11Integral) (h1 : TYZLcalOne) (h29 : TYZLemma29Mod2)
    (hS : Shimura.ShimuraReciprocityModFn)
    (h318 : Lemma318Literal HHprime) (h35 : ∀ ℓ : ℕ → ℤ, IsTYZLcal ℓ → Thm35First ℓ tyzZ) :
    ZInQ.Literature.TYZThm35ReadingA :=
  tyzThm35ReadingA_of_lcal_shimuraModFn_lemma318_thm35First_betaOneLift h11 h1 h29 hS h318 h35
    betaOneLiftExists'

end Main

end ZInQ.Contrib.TYZGenus.T321
