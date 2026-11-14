import ZInQKernel.Contrib.TYZGenus.RingClassBridge
import ZInQKernel.Contrib.TYZGenus.ShimuraFricke

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

/-! ### Absolute Frobenius elements (copied from `ZInQKernel/Contrib/Chebotarev/FrobeniusDenseOfExists.lean`,
namespace `ZInQ.Contrib.ChebFD.C10`, with `GQ` renamed `GalQ`; that module imports all of Mathlib) -/

/-- `\bar ℤ`. -/
abbrev Zbar : Type := integralClosure ℤ Qbar

/-- `𝓞_E → \bar ℤ`. -/
noncomputable def toZbar (E : IntermediateField ℚ Qbar) : 𝓞 E →+* Zbar :=
  RingHom.codRestrict ((algebraMap E Qbar).comp (algebraMap (𝓞 E) E)) (integralClosure ℤ Qbar)
    (fun x => (RingOfIntegers.isIntegral_coe x).map (IsScalarTower.toAlgHom ℤ E Qbar))

@[simp] lemma toZbar_coe (E : IntermediateField ℚ Qbar) (x : 𝓞 E) :
    ((toZbar E x : Zbar) : Qbar) = ((x : E) : Qbar) := rfl

lemma card_quot (p : ℕ) [Fact p.Prime] : Nat.card (ℤ ⧸ Ideal.span {(p : ℤ)}) = p := by
  rw [Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

/-- The Frobenius condition at `𝔓` on the elements of `\bar ℤ` lying in `F`. -/
def FrobOn (p : ℕ) (P : Ideal Zbar) (F : IntermediateField ℚ Qbar) : Set GalQ :=
  {h | ∀ x y : Zbar, (x : Qbar) ∈ F → (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P}

/-- Finite layer of the absolute Frobenius (copied from `ZInQKernel/Contrib/Chebotarev/FrobeniusDenseOfExists.lean`). -/
def FrobExistsFinite : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Ideal Zbar) [P.IsPrime], P.under ℤ = Ideal.span {(p : ℤ)} →
    ∀ (F : IntermediateField ℚ Qbar) [FiniteDimensional ℚ F] [IsGalois ℚ F],
      (FrobOn p P F).Nonempty

/-- Absolute Frobenius at a prime of `\bar ℤ` (copied). -/
def FrobExistsAt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (P : Ideal Zbar) [P.IsPrime], P.under ℤ = Ideal.span {(p : ℤ)} →
    ∃ h : GalQ, ∀ x y : Zbar, (y : Qbar) = h (x : Qbar) - (x : Qbar) ^ p → y ∈ P


lemma frobOn_anti {p : ℕ} {P : Ideal Zbar} {F F' : IntermediateField ℚ Qbar} (hF : F ≤ F') :
    FrobOn p P F' ⊆ FrobOn p P F :=
  fun _ hh x y hx hy => hh x y (hF hx) hy

lemma isClosed_frobOn (p : ℕ) (P : Ideal Zbar) (F : IntermediateField ℚ Qbar)
    [FiniteDimensional ℚ F] : IsClosed (FrobOn p P F) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro h hh
  simp only [FrobOn, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hh
  obtain ⟨x, y, hx, hy, hyP⟩ := hh
  refine ⟨(fun k => h⁻¹ * k) ⁻¹' (F.fixingSubgroup : Set GalQ), ?_, ?_, ?_⟩
  · intro k hk hk'
    have hfix := (IntermediateField.mem_fixingSubgroup_iff F _).mp hk (x : Qbar) hx
    change h⁻¹ (k (x : Qbar)) = (x : Qbar) at hfix
    have hkx : k (x : Qbar) = h (x : Qbar) := by
      have e := congrArg h hfix
      rwa [show h (h⁻¹ (k (x : Qbar))) = k (x : Qbar) from AlgEquiv.apply_symm_apply h _] at e
    exact hyP (hk' x y hx (by rw [hy, hkx]))
  · exact (IntermediateField.fixingSubgroup_isOpen F).preimage (continuous_const.mul continuous_id)
  · simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact one_mem _

instance : IsGalois ℚ Qbar := ⟨⟩

/-- **Step (b) from its finite layer (GLUE, proved): compactness of `G_ℚ`.** -/
theorem frobExistsAt_of_finite (hf : FrobExistsFinite) : FrobExistsAt := by
  intro p _ P _ hP
  let ι := {F : IntermediateField ℚ Qbar // FiniteDimensional ℚ F}
  have : Nonempty ι := ⟨⟨⊥, inferInstance⟩⟩
  let t : ι → Set GalQ := fun F => FrobOn p P F.1
  have htd : Directed (· ⊇ ·) t := by
    rintro ⟨F₁, h₁⟩ ⟨F₂, h₂⟩
    refine ⟨⟨F₁ ⊔ F₂, inferInstance⟩, frobOn_anti le_sup_left, frobOn_anti le_sup_right⟩
  have htn : ∀ F, (t F).Nonempty := by
    rintro ⟨F, hF⟩
    let N := IntermediateField.normalClosure ℚ F Qbar
    have : FiniteDimensional ℚ N := normalClosure.is_finiteDimensional ℚ F Qbar
    have : Normal ℚ N := normalClosure.normal ℚ F Qbar
    have : IsGalois ℚ N := ⟨⟩
    exact (hf p P hP N).mono (frobOn_anti F.le_normalClosure)
  have htcl : ∀ F, IsClosed (t F) := fun F => by
    have := F.2
    exact isClosed_frobOn p P F.1
  obtain ⟨h, hh⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn
    (fun F => (htcl F).isCompact) htcl
  refine ⟨h, fun x y hy => ?_⟩
  have hxi : IsIntegral ℚ (x : Qbar) := Algebra.IsIntegral.isIntegral _
  have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {(x : Qbar)}) :=
    IntermediateField.adjoin.finiteDimensional hxi
  exact Set.mem_iInter.mp hh ⟨IntermediateField.adjoin ℚ {(x : Qbar)}, this⟩ x y
    (IntermediateField.mem_adjoin_simple_self ℚ _) hy

/-- **Step (b), finite layer (GLUE, proved from Mathlib).** -/
theorem frobExistsFinite : FrobExistsFinite := by
  intro p _ P _ hP F _ _
  have : NumberField F := ⟨⟩
  set QF := P.comap (toZbar F) with hQF
  have hQFp : QF.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [← hP, Ideal.under, Ideal.under, hQF, Ideal.comap_comap]
    congr 1
  have hQFprime : QF.IsPrime := Ideal.comap_isPrime _ _
  have hQFne : QF ≠ ⊥ := by
    intro h0
    have hp : ((p : ℤ) : 𝓞 F) ∈ QF := by
      change algebraMap ℤ (𝓞 F) (p : ℤ) ∈ QF
      rw [← Ideal.mem_comap]
      change (p : ℤ) ∈ QF.under ℤ
      rw [hQFp]
      exact Ideal.mem_span_singleton_self _
    rw [h0, Ideal.mem_bot] at hp
    have : ((p : ℤ) : 𝓞 F) ≠ 0 := by
      have := (Fact.out : p.Prime).ne_zero
      exact_mod_cast this
    exact this hp
  have : QF.IsMaximal := hQFprime.isMaximal hQFne
  let _ := IsIntegralClosure.MulSemiringAction ℤ ℚ F (𝓞 F)
  have := Algebra.isInvariant_of_isGalois ℤ ℚ F (𝓞 F)
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ (F ≃ₐ[ℚ] F) QF
  obtain ⟨h, hres⟩ : ∃ h : GalQ, AlgEquiv.restrictNormal h F = σ :=
    ⟨σ.liftNormal Qbar, σ.restrict_liftNormal Qbar⟩
  subst hres
  refine ⟨h, fun x y hx hy => ?_⟩
  have hxi : IsIntegral ℤ (⟨(x : Qbar), hx⟩ : F) := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F Qbar) (algebraMap F Qbar).injective]
    exact x.2
  let x' : 𝓞 F := ⟨⟨(x : Qbar), hx⟩, hxi⟩
  have hmem := hσ x'
  rw [hQFp, card_quot, hQF, Ideal.mem_comap] at hmem
  convert hmem using 1
  apply Subtype.ext
  rw [hy, map_sub, map_pow, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, toZbar_coe,
    toZbar_coe]
  congr 1
  change h (x : Qbar) = ((algebraMap (𝓞 F) F (galRestrict ℤ ℚ F (𝓞 F) _ x')) : Qbar)
  rw [algebraMap_galRestrict_apply]
  exact (AlgEquiv.restrictNormal_commutes h F (algebraMap (𝓞 F) F x')).symm


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
