import ZInQKernel.Contrib.OneProof.TYZGenusFold.Jacobi
import ZInQKernel.Contrib.OneProof.TYZGenusFold.Local
import ZInQKernel.Contrib.OneProof.TYZGenusFold.Ideles

/-!
# tyz-genus: `f_n` vanishes on the classes with `χ_U = Π_{q ∣ n} χ_q = −1` (`n ≡ 1 (mod 8)`), and TYZ Lemma 2.8

For a class `t` take an integral ideal `I ∈ t` with `N I` prime to `2n`, an `α ∈ I` with `(α) = I M`,
`M + (N I) = O`, and the idele `a = aK (N I) α` (class `[I] = t`). If `τ̂(a) ∈ B^× twoRep(t') H`, the reduced
norms give `N I · nrd(twoRep t') ≡ 1 (mod 4)`; genus theory gives `χ_U(t) = χ₄(N I)`. So `χ_U(t) = −1` forces
`t'.2.2 ≠ 0`, where `F = 0` and hence `f_n = ±F = 0`. Then `χ_{T^c} f_n = χ_T f_n` termwise, which is TYZ
Lemma 2.8.
-/

set_option linter.style.longLine false
set_option autoImplicit false

noncomputable section

namespace ZInQ.Contrib.TYZGenusFold

open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.TYZDecomp.H29Genus ZInQ.Contrib.T21Proof
  ZInQ.Contrib.HfxProof ZInQ.Contrib.HP23Proof
open ZInQ.RouteK.Redei ZInQ.RouteK.Rank5b
open ZInQ.Contrib.TYZGenus.TYZ35 (gchar divSet sgn2 divSet_div)
open IsDedekindDomain NumberField
open scoped Quaternion nonZeroDivisors

local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩

variable {n : ℕ} [NeZero n]

/-! ### Ideals prime to `m` -/

theorem coprime_absNorm_of_sup {M : Ideal (𝓞 (QNeg n))} {m : ℕ}
    (h : M ⊔ Ideal.span {((m : ℕ) : 𝓞 (QNeg n))} = ⊤) : Nat.Coprime (Ideal.absNorm M) m := by
  refine Nat.Coprime.symm (Nat.coprime_of_dvd fun k hk hkm hkM => ?_)
  have hle : Ideal.span {((m : ℕ) : 𝓞 (QNeg n))} ≤ Ideal.span {((k : ℕ) : 𝓞 (QNeg n))} := by
    rw [Ideal.span_singleton_le_span_singleton]
    exact_mod_cast (Nat.cast_dvd_cast hkm : ((k : ℕ) : 𝓞 (QNeg n)) ∣ ((m : ℕ) : 𝓞 (QNeg n)))
  have htop : M ⊔ Ideal.span {((k : ℕ) : 𝓞 (QNeg n))} = ⊤ :=
    top_le_iff.mp (h ▸ sup_le_sup_left hle M)
  exact not_dvd_absNorm_of_sup_span_eq_top hk htop hkM

/-- Every class contains an integral ideal with norm prime to a given `m > 1`. -/
theorem exists_mk0_coprime_nat {m : ℕ} (hm : 1 < m) (c : ClassGroup (𝓞 (QNeg n))) :
    ∃ I : (Ideal (𝓞 (QNeg n)))⁰, ClassGroup.mk0 I = c ∧
      Nat.Coprime (Ideal.absNorm (I : Ideal (𝓞 (QNeg n)))) m := by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective c⁻¹
  have hJ0 : (J : Ideal (𝓞 (QNeg n))) ≠ 0 := nonZeroDivisors.coe_ne_zero J
  have hq0 : Ideal.span {(m : 𝓞 (QNeg n))} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact natCast_ne_zero_O (by omega)
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
    (I := (J : Ideal (𝓞 (QNeg n))) * Ideal.span {(m : 𝓞 (QNeg n))}) (J := J)
    (Ideal.mul_le_inf.trans inf_le_left) (mul_ne_zero hJ0 hq0)
  have haJ : a ∈ (J : Ideal (𝓞 (QNeg n))) := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨M, hM⟩ := Ideal.dvd_span_singleton.2 haJ
  have hcop : M ⊔ Ideal.span {(m : 𝓞 (QNeg n))} = ⊤ := by
    have h1 : (J : Ideal (𝓞 (QNeg n))) * (Ideal.span {(m : 𝓞 (QNeg n))} ⊔ M) = J * ⊤ := by
      rw [Ideal.mul_sup, ← hM, ha, Ideal.mul_top]
    rw [sup_comm]; exact mul_left_cancel₀ hJ0 h1
  have hM0 : M ≠ 0 := by
    rintro rfl
    rw [Ideal.zero_eq_bot, bot_sup_eq, Ideal.span_singleton_eq_top, isUnit_iff_dvd_one,
      show (1 : 𝓞 (QNeg n)) = ((1 : ℕ) : 𝓞 (QNeg n)) by simp, natCast_dvd_natCast_iff] at hcop
    exact hm.ne' (Nat.dvd_one.1 hcop)
  set M' : (Ideal (𝓞 (QNeg n)))⁰ := ⟨M, mem_nonZeroDivisors_of_ne_zero hM0⟩
  refine ⟨M', ?_, coprime_absNorm_of_sup hcop⟩
  have h1 : ClassGroup.mk0 J * ClassGroup.mk0 M' = 1 := by
    rw [← map_mul, ClassGroup.mk0_eq_one_iff (J * M').2]
    have e : ((J * M' : (Ideal (𝓞 (QNeg n)))⁰) : Ideal (𝓞 (QNeg n))) = Ideal.span {a} := by
      rw [Submonoid.coe_mul]; exact hM.symm
    rw [e]
    exact ⟨⟨a, rfl⟩⟩
  rw [hJ] at h1
  exact (inv_mul_eq_one.1 h1).symm

/-- An `α ∈ I` with `(α) = I M`, `M + (N I) = O`. -/
theorem exists_alpha (I : (Ideal (𝓞 (QNeg n)))⁰) :
    ∃ α : 𝓞 (QNeg n), ((α : QNeg n)) ≠ 0 ∧ ∃ M : Ideal (𝓞 (QNeg n)),
      Ideal.span {α} = (I : Ideal (𝓞 (QNeg n))) * M ∧
      M ⊔ Ideal.span {((Ideal.absNorm (I : Ideal (𝓞 (QNeg n))) : ℕ) : 𝓞 (QNeg n))} = ⊤ := by
  set m := Ideal.absNorm (I : Ideal (𝓞 (QNeg n)))
  have hI0 : (I : Ideal (𝓞 (QNeg n))) ≠ 0 := nonZeroDivisors.coe_ne_zero I
  have hm0 : m ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hI0
  have hq0 : Ideal.span {(m : 𝓞 (QNeg n))} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact natCast_ne_zero_O hm0
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
    (I := (I : Ideal (𝓞 (QNeg n))) * Ideal.span {(m : 𝓞 (QNeg n))}) (J := I)
    (Ideal.mul_le_inf.trans inf_le_left) (mul_ne_zero hI0 hq0)
  have haI : a ∈ (I : Ideal (𝓞 (QNeg n))) := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨M, hM⟩ := Ideal.dvd_span_singleton.2 haI
  have hcop : M ⊔ Ideal.span {(m : 𝓞 (QNeg n))} = ⊤ := by
    have h1 : (I : Ideal (𝓞 (QNeg n))) * (Ideal.span {(m : 𝓞 (QNeg n))} ⊔ M) = I * ⊤ := by
      rw [Ideal.mul_sup, ← hM, ha, Ideal.mul_top]
    rw [sup_comm]; exact mul_left_cancel₀ hI0 h1
  by_cases ha0 : a = 0
  · -- then `I (m) = I`, so `(m) = O`, `m = 1`, `I = O`: take `α = 1`
    have h1 : (I : Ideal (𝓞 (QNeg n))) * Ideal.span {(m : 𝓞 (QNeg n))} = I * ⊤ := by
      rw [Ideal.mul_top]; rw [ha0, Ideal.span_singleton_eq_bot.mpr rfl, sup_bot_eq] at ha; exact ha
    have hmt : Ideal.span {(m : 𝓞 (QNeg n))} = ⊤ := mul_left_cancel₀ hI0 h1
    have hm1 : m = 1 := by
      rw [Ideal.span_singleton_eq_top, isUnit_iff_dvd_one,
        show (1 : 𝓞 (QNeg n)) = ((1 : ℕ) : 𝓞 (QNeg n)) by simp, natCast_dvd_natCast_iff] at hmt
      exact Nat.dvd_one.1 hmt
    have hItop : (I : Ideal (𝓞 (QNeg n))) = ⊤ := Ideal.absNorm_eq_one_iff.mp hm1
    refine ⟨1, by simp, ⊤, by rw [hItop, Ideal.span_singleton_one, Ideal.top_mul], top_sup_eq _⟩
  · refine ⟨a, ?_, M, hM, hcop⟩
    intro h
    apply ha0
    exact RingOfIntegers.ext (by simpa using h)

/-! ### Reduced norm of `τ(x)` -/

theorem normSq_tau (h1 : n % 8 = 1) {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]} (hτ : AdmissibleTau n τ) (x : QNeg n) :
    Quaternion.normSq (τ x) = Algebra.norm ℚ x := by
  obtain ⟨a, b, c, hτω, hn, -⟩ := exists_abc hτ (Or.inl h1)
  rw [tau_apply, hτω, algNorm_eq n, QuadraticAlgebra.norm_def, Quaternion.normSq_def']
  have hn' : (n : ℚ) = (a : ℚ) ^ 2 + (b : ℚ) ^ 2 + (c : ℚ) ^ 2 := by exact_mod_cast hn
  simp
  linear_combination (-(x.im ^ 2)) * hn'

theorem nrdH_βZ_mod4_one : ∀ t : T8, t.2.2 = 0 → nrdH (βZ t) % 4 = 1 := by decide +kernel

omit [NeZero n] in
theorem odd_of_coprime_two_mul {m : ℕ} (h : Nat.Coprime m (2 * n)) : m % 2 = 1 := by
  have h2 : Nat.Coprime m 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 n) h
  rcases Nat.mod_two_eq_zero_or_one m with h0 | h0
  · exact absurd (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm h2) (Nat.dvd_of_mod_eq_zero h0))
      (by norm_num)
  · exact h0

/-- Valuation parity at an odd place: `A = g c² e`, `e` a unit, gives `v(gA)` even. -/
theorem even_val_mul {p : ℕ} [Fact p.Prime] {g A : ℚ} (hg : g ≠ 0) (hA : A ≠ 0) {c e : ℚ_[p]} (hc : c ≠ 0)
    (he : ‖e‖ = 1) (h : (A : ℚ_[p]) = (g : ℚ_[p]) * (c ^ 2 * e)) : Even (padicValRat p (g * A)) := by
  refine even_padicValRat_of_eq (mul_ne_zero hg hA) (a := (A : ℚ_[p])) (by exact_mod_cast hA) hc he ?_
  push_cast
  rw [pow_two]
  nth_rewrite 1 [h]
  ring

/-- **`f_n` vanishes on the classes with `Π_{q ∣ n} χ_q = −1`** (`n ≡ 1 (mod 8)`). -/
theorem tv_zero_of_gchar (hsq : Squarefree n) (h1 : n % 8 = 1) {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]}
    (hτ : AdmissibleTau n τ) {f : ℍ[AQ] → ℤ} (hf : IsTestVector n τ f) (t : ClassGroup (𝓞 (QNeg n)))
    (ht : gchar n Finset.univ t = -1) : f ((tauHatU n τ (clLift n t) : ℍ[AQ]ˣ) : ℍ[AQ]) = 0 := by
  obtain ⟨v, hv, F, hP, hodd, C, hH, hC⟩ := partition_one8 hsq h1 hτ
  obtain ⟨s, -, hfs⟩ := tv_eq_sign hv hP hf
  have hF0 := F_zero hv hP hodd C hH hC
  have hn1 : 1 < 2 * n := by have := NeZero.ne n; omega
  obtain ⟨I, hIt, hcop⟩ := exists_mk0_coprime_nat hn1 t
  obtain ⟨α, hα, M, hspan, hM⟩ := exists_alpha I
  set m := Ideal.absNorm (I : Ideal (𝓞 (QNeg n))) with hmdef
  have hcl := toClassGroup_aKU hα hspan hM
  rw [tv_eq_of_toClassGroup_eq hf.1 (x := clLift n t) (y := aKU n m (α : QNeg n) hα)
    (by rw [toClassGroup_clLift, hcl, hIt])]
  obtain ⟨t', ht'⟩ := hP.1 (tauHatU n τ (aKU n m (α : QNeg n) hα))
  rw [hfs _ t' ht']
  suffices h : t'.2.2 ≠ 0 by rw [hF0 t' h, mul_zero]
  intro h0
  have hm2 : m % 2 = 1 := odd_of_coprime_two_mul hcop
  have hg := gchar_univ_mk0 (by omega) hsq I hcop t hIt
  rw [ht] at hg
  have hm3 : m % 4 = 3 := by
    by_contra hne
    have h41 : m % 4 = 1 := by omega
    rw [if_pos h41] at hg
    norm_num at hg
  have hβ := nrdH_βZ_mod4_one t' h0
  obtain ⟨g, hgpos, hoddw, κ, hκ, h2⟩ := dc_norm hv C hH hC ht'
  have hy : ∀ w, piQ w ((tauHatU n τ (aKU n m (α : QNeg n) hα) : ℍ[AQ]ˣ) : ℍ[AQ]) =
      if (Pw w : ℕ) ∣ m then qp (Pw w : ℕ) (τ α) else 1 := fun w => piQ_tauHat_aK τ m α w
  have hNα : Quaternion.normSq (τ (α : QNeg n)) = ((m * Ideal.absNorm M : ℕ) : ℚ) := by
    have e1 : ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℤ) = Algebra.norm ℤ α := by
      rw [Ideal.absNorm_span_singleton, Int.natCast_natAbs, abs_of_nonneg (normZ_nonneg α)]
    rw [normSq_tau h1 hτ, algNorm_coe, ← e1, hspan, map_mul]
    push_cast
    rfl
  have hNM : Nat.Coprime (Ideal.absNorm M) m := coprime_absNorm_of_sup hM
  have hm0 : m ≠ 0 := by omega
  have hNM0 : Ideal.absNorm M ≠ 0 := by
    intro h; rw [h, Nat.coprime_zero_left] at hNM; omega
  have hev : ∀ r : ℕ, r.Prime → r ≠ 2 → Even (padicValRat r (g * m)) := by
    intro r hr hr2
    have := Fact.mk hr
    obtain ⟨w, hw⟩ := exists_place_of_prime r hr
    have hwv : w ≠ v := fun h' => hr2 (by rw [← hw, h']; exact Pw_eq_two hv)
    obtain ⟨c, e, hc, he, hN⟩ := hoddw w hwv
    rw [hy w] at hN
    have hgm : padicValRat r (g * m) = padicValRat r g + padicValRat r (m : ℚ) :=
      padicValRat.mul hgpos.ne' (by exact_mod_cast hm0)
    by_cases hrm : r ∣ m
    · rw [if_pos (hw ▸ hrm), normSq_qp, hNα] at hN
      have hA : ((m * Ideal.absNorm M : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.mul_ne_zero hm0 hNM0
      have hE := even_val_mul (p := (Pw w : ℕ)) hgpos.ne' hA hc he (by exact_mod_cast hN)
      rw [hw] at hE
      have hrM : ¬ r ∣ Ideal.absNorm M := fun h' =>
        hr.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hNM h' hrm)
      rw [Nat.cast_mul, ← mul_assoc, padicValRat.mul (mul_ne_zero hgpos.ne' (by exact_mod_cast hm0))
        (by exact_mod_cast hNM0), padicValRat.of_nat (n := Ideal.absNorm M),
        padicValNat.eq_zero_of_not_dvd hrM, Nat.cast_zero, add_zero] at hE
      exact hE
    · rw [if_neg (by rw [hw]; exact hrm), map_one] at hN
      have hE := even_padicValRat_of_eq (p := (Pw w : ℕ)) hgpos.ne' one_ne_zero hc he (by rw [one_pow, hN])
      rw [hw] at hE
      rw [hgm, padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hrm, Nat.cast_zero, add_zero]
      exact hE
  have hv2 : ¬ (Pw v : ℕ) ∣ m := by rw [Pw_eq_two hv]; omega
  rw [hy v, if_neg hv2, map_one] at h2
  have key : ∀ (p : ℕ) [Fact p.Prime], p = 2 → ∀ (κ : ℚ_[p]) (b : ℤ), Good κ → b % 4 = 1 →
      (1 : ℚ_[p]) = (g : ℚ_[p]) * ((b : ℤ) : ℚ_[p]) * κ → False := by
    intro p _ hp
    subst hp
    intro κ b hκ hb e2
    have hgm : Good (((g * m : ℚ)) : ℚ_[2]) := good_rat (mul_pos hgpos (by exact_mod_cast Nat.pos_of_ne_zero hm0)) hev
    have hgb : Good ((g : ℚ_[2]) * ((b : ℤ) : ℚ_[2])) := by
      have h1' : Good ((g : ℚ_[2]) * ((b : ℤ) : ℚ_[2]) * κ) := by rw [← e2]; exact Good.one
      exact h1'.of_mul_right hκ
    have hg0 : (g : ℚ_[2]) ≠ 0 := by exact_mod_cast hgpos.ne'
    have hmb : Good ((((m : ℤ) * b : ℤ)) : ℚ_[2]) := by
      have e3 : ((((m : ℤ) * b : ℤ)) : ℚ_[2]) =
          ((g * m : ℚ) : ℚ_[2]) * ((g : ℚ_[2]) * ((b : ℤ) : ℚ_[2])) / (g : ℚ_[2]) ^ 2 := by
        push_cast; field_simp
      rw [e3]
      exact (hgm.mul hgb).div (good_sq hg0)
    have hmod : ((m : ℤ) * b) % 4 = 3 := by
      rw [Int.mul_emod, hb]
      have : (m : ℤ) % 4 = 3 := by exact_mod_cast hm3
      rw [this]; rfl
    exact not_good_int hmod hmb
  exact key _ (Pw_eq_two hv) κ _ hκ hβ h2

theorem gchar_eq_one_or (T : Finset n.primeFactors) (c : ClassGroup (𝓞 (QNeg n))) :
    gchar n T c = 1 ∨ gchar n T c = -1 := by
  unfold gchar
  refine Finset.prod_induction _ (fun x => x = 1 ∨ x = -1) ?_ (Or.inl rfl) ?_
  · rintro a b (rfl | rfl) (rfl | rfl) <;> simp
  · intro q _; unfold sgn2; split_ifs <;> simp


end ZInQ.Contrib.TYZGenusFold
