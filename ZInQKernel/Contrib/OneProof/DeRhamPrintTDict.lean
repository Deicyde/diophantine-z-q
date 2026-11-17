import ZInQKernel.Contrib.G9.KerTheta

/-!
# derham-print (dictionary): `t = log[ε]` in the kernel's `B_dR^+`, and `B_dR ≅ B_dR^+[1/t]`

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task derham-print, 2026-11-16).

The kernel's `B_dR` is Mathlib's `BDeRham 𝓞_ℂ_p p` (`B_dR^+` inverted at the generators of `ker θ`); bdr-kertheta
(`ZInQKernel/Contrib/G9/KerTheta.lean`) proved that `B_dR^+` is a `ξ`-adically complete DVR with maximal ideal
`(ξ)`, `ξ = p - [p♭]`, that `B_dR` is its fraction field and that `B_dR ≅ B_dR^+[1/ξ]`. A print that defines
`B_dR = Frac(B_dR^+)` or `B_dR^+[1/ξ]` is therefore matched at the level of definitions. A print that defines
`B_dR = B_dR^+[1/t]` with `t = log[ε]` (Berger; OPEN.md's kernel-wide B_dR reading) needed `t ≠ 0`, which was
open because `t` was not constructed. This file constructs it and closes that step:

* `RootSystem p`: a compatible system `ζ₀ = 1, ζ₁ ≠ 1, ζ_{n+1}^p = ζ_n` in `𝓞_ℂ_p` (any one: the statements
  below hold for every choice); `rootSystem p` shows one exists.
* `eps Z = (1, ζ_p, ζ_{p²}, …) ∈ 𝓞_ℂ_p♭`, `xe Z = [ε] - 1 ∈ B_dR^+`, and `tt p Z = log[ε]`, the `ξ`-adic sum
  of `Σ_{n ≥ 1} (-1)^{n+1} ([ε] - 1)^n / n` (`logPlus`; unique limit: `logPlus_unique`).
* `ker_theta_eq_omega`: `ker θ = (ω)` in `W(𝓞_ℂ_p♭)`, `ω = Σ_{i<p} [ε^{1/p}]^i` (Fontaine's generator), from
  `‖ζ_{p²} - 1‖^{p(p-1)} ≥ ‖p‖` (`Φ_{p²}(1) = p`) and the divisibility of `p♭` by `(ε^{1/p} - 1)^{p-1}` in the tilt.
* `tt_eq_varpi_mul_unit`: **`t = ξ · unit`** (so `t ≠ 0`, `tt_ne_zero`): `[ε] - 1 = ω · ([ε^{1/p}] - 1)` with
  `[ε^{1/p}] - 1` a unit of `B_dR^+` (`θ = ζ_p - 1 ≠ 0`) and `ω ∉ (ξ²)`, and `log(1 + x) ≡ x (mod x²)`.
* `bdREquivAwayT`: **`B_dR ≅ B_dR^+[1/t]` as `B_dR^+`-algebras**; `ext_of_extends` and `transport_extends`: the
  Galois action a print puts on `B_dR^+[1/t]` (the extension of the action on `B_dR^+`) is the transport of the
  kernel's (pkg-I4's `bdrAct σ` is by definition the `IsLocalization.map` of `bdrPlusMap σ`, I4Layer.lean l. 403).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace DeRhamPrint.TDict

open Ideal WittVector ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4.Cp ZInQ.Contrib.G9.BdrKer
  ZInQ.Contrib.G9.BdrKer.Cp

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]


/-! ## 1. Elements of the tilt from compatible sequences -/

/-- `(z₀, z₁, …) ∈ O♭` for a sequence with `z (n+1) ^ p = z n` in `O`. -/
def mkSeq (z : ℕ → (𝓞_ℂ_[p] : Type)) (hz : ∀ n, z (n + 1) ^ p = z n) : PreTilt (𝓞_ℂ_[p] : Type) p :=
  ⟨fun n => Ideal.Quotient.mk _ (z n), fun n => by rw [← map_pow, hz]⟩

theorem coeff_mkSeq (z : ℕ → (𝓞_ℂ_[p] : Type)) (hz : ∀ n, z (n + 1) ^ p = z n) (n : ℕ) :
    PreTilt.coeff n (mkSeq p z hz) = Ideal.Quotient.mk _ (z n) := rfl

theorem pow_seq (z : ℕ → (𝓞_ℂ_[p] : Type)) (hz : ∀ n, z (n + 1) ^ p = z n) (n : ℕ) : z n ^ p ^ n = z 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, hz, ih]

theorem untilt_mkSeq (z : ℕ → (𝓞_ℂ_[p] : Type)) (hz : ∀ n, z (n + 1) ^ p = z n) : (mkSeq p z hz).untilt = z 0 := by
  rw [IsHausdorff.eq_iff_smodEq (I := span {(p : (𝓞_ℂ_[p] : Type))})]
  intro n
  rw [SModEq.sub_mem, mem_span_pow_iff']
  have h1 : root (mkSeq p z hz) n - z n ∈ span {(p : (𝓞_ℂ_[p] : Type))} := by
    rw [← Ideal.Quotient.eq, mk_root]; rfl
  have h2 := dvd_sub_pow_of_dvd_sub (Ideal.mem_span_singleton.mp h1) n
  rw [root_pow, pow_seq p z hz] at h2
  obtain ⟨c, hc⟩ := h2
  exact ⟨p * c, by rw [hc]; ring⟩

/-! ## 2. Divisibility in the tilt by comparing absolute values of untilts -/

/-- If `‖c♯‖ ≤ ‖a♯‖` and `a♯ ≠ 0`, then `a ∣ c` in `O♭` (bdr-kertheta's `dvd_of_coeff_zero`, with `p♭`
replaced by any `a`). -/
theorem dvd_of_norm_le (a c : PreTilt (𝓞_ℂ_[p] : Type) p) (ha : ((a.untilt : (𝓞_ℂ_[p] : Type)) : ℂ_[p]) ≠ 0)
    (hle : ‖((c.untilt : (𝓞_ℂ_[p] : Type)) : ℂ_[p])‖ ≤ ‖((a.untilt : (𝓞_ℂ_[p] : Type)) : ℂ_[p])‖) : ∃ d, c = a * d := by
  have han : ∀ n, ‖((root a n : (𝓞_ℂ_[p] : Type)) : ℂ_[p])‖ ^ p ^ n = ‖((a.untilt : (𝓞_ℂ_[p] : Type)) : ℂ_[p])‖ := fun n => by
    have h := congrArg (fun z : (𝓞_ℂ_[p] : Type) => ‖(z : ℂ_[p])‖) (root_pow a n)
    simpa [norm_pow] using h
  have hcn : ∀ n, ‖((root c n : (𝓞_ℂ_[p] : Type)) : ℂ_[p])‖ ^ p ^ n = ‖((c.untilt : (𝓞_ℂ_[p] : Type)) : ℂ_[p])‖ := fun n => by
    have h := congrArg (fun z : (𝓞_ℂ_[p] : Type) => ‖(z : ℂ_[p])‖) (root_pow c n)
    simpa [norm_pow] using h
  have hne : ∀ n, ((root a n : (𝓞_ℂ_[p] : Type)) : ℂ_[p]) ≠ 0 := fun n h0 => by
    have := han n
    rw [h0, norm_zero, zero_pow (pow_ne_zero _ hp.out.ne_zero)] at this
    exact ha (norm_eq_zero.mp this.symm)
  have hle' : ∀ n, ‖((root c n : (𝓞_ℂ_[p] : Type)) : ℂ_[p])‖ ≤ ‖((root a n : (𝓞_ℂ_[p] : Type)) : ℂ_[p])‖ := fun n => by
    have hpn : p ^ n ≠ 0 := pow_ne_zero _ hp.out.ne_zero
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) hpn).mp ?_
    rw [hcn, han]; exact hle
  let e : ℕ → (𝓞_ℂ_[p] : Type) := fun n => ⟨((root c n : (𝓞_ℂ_[p] : Type)) : ℂ_[p]) / ((root a n : (𝓞_ℂ_[p] : Type)) : ℂ_[p]),
    (mem_O_iff p _).mpr (by
      rw [norm_div]; exact div_le_one_of_le₀ (hle' n) (norm_nonneg _))⟩
  have he : ∀ n, e (n + 1) ^ p = e n := fun n => by
    apply Subtype.ext
    simp only [e, SubmonoidClass.coe_pow, div_pow]
    rw [← SubmonoidClass.coe_pow, ← SubmonoidClass.coe_pow, root_succ_pow, root_succ_pow]
  have hce : ∀ n, root c n = root a n * e n := fun n => by
    apply Subtype.ext
    simp only [e, MulMemClass.coe_mul]
    field_simp [hne n]
  let d : PreTilt (𝓞_ℂ_[p] : Type) p := ⟨fun n => Ideal.Quotient.mk _ (e n), fun n => by
    rw [← map_pow, he]⟩
  refine ⟨d, ?_⟩
  apply Perfection.ext
  intro n
  change PreTilt.coeff n c = PreTilt.coeff n (a * d)
  rw [map_mul]
  change PreTilt.coeff n c = PreTilt.coeff n a * Ideal.Quotient.mk _ (e n)
  rw [← mk_root, ← mk_root, ← map_mul, hce]

/-! ## 3. A system of `p`-power roots of unity, and `‖ζ_{p²} - 1‖^{p(p-1)} ≥ ‖p‖` -/

/-- A compatible system `ζ₀ = 1, ζ₁ ≠ 1, ζ_{n+1}^p = ζ_n` of `p`-power roots of unity in `𝓞_ℂ_p`. -/
structure RootSystem where
  z : ℕ → (𝓞_ℂ_[p] : Type)
  pow_succ : ∀ n, z (n + 1) ^ p = z n
  zero : z 0 = 1
  one_ne : z 1 ≠ 1

variable {p}

theorem norm_one_sub_pow_le (ζ : (𝓞_ℂ_[p] : Type)) (k : ℕ) :
    ‖(1 : ℂ_[p]) - (ζ : ℂ_[p]) ^ k‖ ≤ ‖(1 : ℂ_[p]) - (ζ : ℂ_[p])‖ := by
  have h : (1 : (𝓞_ℂ_[p] : Type)) - ζ ^ k = (1 - ζ) * ∑ i ∈ Finset.range k, ζ ^ i := (mul_neg_geom_sum ζ k).symm
  have h' := congrArg (fun z : (𝓞_ℂ_[p] : Type) => ‖(z : ℂ_[p])‖) h
  simp only [MulMemClass.coe_mul] at h'
  push_cast at h'
  rw [h', norm_mul]
  have hs := norm_le_one p (∑ i ∈ Finset.range k, ζ ^ i)
  push_cast at hs
  calc ‖(1 : ℂ_[p]) - ζ‖ * ‖∑ i ∈ Finset.range k, (ζ : ℂ_[p]) ^ i‖ ≤ ‖(1 : ℂ_[p]) - ζ‖ * 1 :=
        mul_le_mul_of_nonneg_left hs (norm_nonneg _)
    _ = _ := mul_one _

theorem isPrimitiveRoot_z2 (Z : RootSystem p) : IsPrimitiveRoot ((Z.z 2 : (𝓞_ℂ_[p] : Type)) : ℂ_[p]) (p ^ 2) := by
  have h1 : ((Z.z 2 : (𝓞_ℂ_[p] : Type)) : ℂ_[p]) ^ p ^ 1 ≠ 1 := by
    intro h
    apply Z.one_ne
    apply Subtype.ext
    rw [pow_one] at h
    rw [← Z.pow_succ 1]
    push_cast
    exact h
  have h2 : ((Z.z 2 : (𝓞_ℂ_[p] : Type)) : ℂ_[p]) ^ p ^ (1 + 1) = 1 := by
    have := pow_seq p Z.z Z.pow_succ 2
    rw [Z.zero] at this
    have := congrArg (fun z : (𝓞_ℂ_[p] : Type) => (z : ℂ_[p])) this
    simpa using this
  have := orderOf_eq_prime_pow h1 h2
  rw [← this]
  exact IsPrimitiveRoot.orderOf _

theorem norm_p_le (Z : RootSystem p) :
    ‖(p : ℂ_[p])‖ ≤ ‖(1 : ℂ_[p]) - ((Z.z 2 : (𝓞_ℂ_[p] : Type)) : ℂ_[p])‖ ^ (p * (p - 1)) := by
  set ζ : ℂ_[p] := ((Z.z 2 : (𝓞_ℂ_[p] : Type)) : ℂ_[p])
  have hprim := isPrimitiveRoot_z2 Z
  have hev : Polynomial.eval 1 (Polynomial.cyclotomic (p ^ (1 + 1)) ℂ_[p]) = p :=
    Polynomial.eval_one_cyclotomic_prime_pow 1
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hprim, Polynomial.eval_prod] at hev
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hev
  rw [← hev, norm_prod]
  have hcard : (primitiveRoots (p ^ 2) ℂ_[p]).card = p * (p - 1) := by
    rw [hprim.card_primitiveRoots, Nat.totient_prime_pow hp.out (by norm_num)]
    simp
  rw [← hcard, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun μ hμ => ?_
  have hp2 : 0 < p ^ 2 := pow_pos hp.out.pos 2
  have : NeZero (p ^ 2) := ⟨hp2.ne'⟩
  have hμ' : μ ^ p ^ 2 = 1 := ((mem_primitiveRoots hp2).mp hμ).pow_eq_one
  obtain ⟨i, -, rfl⟩ := hprim.eq_pow_of_pow_eq_one hμ'
  exact norm_one_sub_pow_le (Z.z 2) i


/-! ## 4. `ε`, `ε^{1/p}` and `ω = Σ_{i<p} [ε^{1/p}]^i` -/

variable (Z : RootSystem p)

/-- `ε = (1, ζ_p, ζ_{p²}, …) ∈ O♭`. -/
def eps : PreTilt (𝓞_ℂ_[p] : Type) p := mkSeq p Z.z Z.pow_succ

/-- `ε^{1/p} = (ζ_p, ζ_{p²}, …) ∈ O♭`. -/
def eps1 : PreTilt (𝓞_ℂ_[p] : Type) p := mkSeq p (fun n => Z.z (n + 1)) (fun n => Z.pow_succ (n + 1))

theorem untilt_eps : (eps Z).untilt = 1 := by rw [eps, untilt_mkSeq, Z.zero]

theorem untilt_eps1 : (eps1 Z).untilt = Z.z 1 := untilt_mkSeq _ _ _

theorem eps1_pow : eps1 Z ^ p = eps Z := by
  apply Perfection.ext
  intro n
  change PreTilt.coeff n (eps1 Z ^ p) = PreTilt.coeff n (eps Z)
  rw [map_pow, eps1, eps, coeff_mkSeq, coeff_mkSeq, ← map_pow, Z.pow_succ]

theorem eps1_sub_one_ne_zero : eps1 Z - 1 ≠ 0 := by
  intro h
  have h1 : eps1 Z = 1 := sub_eq_zero.mp h
  have h2 := congrArg PreTilt.untilt h1
  rw [untilt_eps1, map_one] at h2
  exact Z.one_ne h2

theorem geom_eq (e : PreTilt (𝓞_ℂ_[p] : Type) p) (he : e - 1 ≠ 0) :
    ∑ i ∈ Finset.range p, e ^ i = (e - 1) ^ (p - 1) := by
  have h1 : (∑ i ∈ Finset.range p, e ^ i) * (e - 1) = (e - 1) ^ (p - 1) * (e - 1) := by
    rw [geom_sum_mul, ← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le, sub_pow_char, one_pow]
  exact mul_right_cancel₀ he h1

theorem sum_z1_eq_zero : ∑ i ∈ Finset.range p, Z.z 1 ^ i = 0 := by
  have h : (∑ i ∈ Finset.range p, Z.z 1 ^ i) * (Z.z 1 - 1) = 0 := by
    rw [geom_sum_mul, Z.pow_succ 0, Z.zero, sub_self]
  exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr Z.one_ne)

/-- `‖(ε^{1/p} - 1)♯‖^{p-1} ≥ ‖p‖`. -/
theorem norm_untilt_pow_ge :
    ‖(p : ℂ_[p])‖ ≤ ‖(((eps1 Z - 1) ^ (p - 1)).untilt : ℂ_[p])‖ := by
  set y := eps1 Z - 1
  set r := ‖((Z.z 2 : (𝓞_ℂ_[p] : Type)) : ℂ_[p]) - 1‖
  have hr : ‖(p : ℂ_[p])‖ ≤ r ^ (p * (p - 1)) := by
    have := norm_p_le Z
    rwa [norm_sub_rev] at this
  have hp1 := norm_p_lt_one p
  have hp0 := norm_p_pos p
  have hrp : ‖(p : ℂ_[p])‖ < r := by
    by_contra hcon
    push Not at hcon
    have h2 : 1 < p * (p - 1) := by
      have := hp.out.two_le
      have h3 : 1 ≤ p - 1 := by omega
      nlinarith
    have := pow_lt_self_of_lt_one₀ hp0 hp1 h2
    have h4 : r ^ (p * (p - 1)) ≤ ‖(p : ℂ_[p])‖ ^ (p * (p - 1)) :=
      pow_le_pow_left₀ (norm_nonneg _) hcon _
    linarith
  -- `root y 1 ≡ ζ_{p²} - 1 (mod p)`
  have hmem : root y 1 - (Z.z 2 - 1) ∈ span {(p : (𝓞_ℂ_[p] : Type))} := by
    rw [← Ideal.Quotient.eq, mk_root, map_sub, map_sub, map_one, eps1, coeff_mkSeq, map_one]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
  have hdiff : ‖((root y 1 - (Z.z 2 - 1) : (𝓞_ℂ_[p] : Type)) : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ := by
    rw [← hc]
    push_cast
    rw [norm_mul]
    have := norm_le_one p c
    nlinarith [norm_nonneg ((c : (𝓞_ℂ_[p] : Type)) : ℂ_[p]), norm_nonneg (p : ℂ_[p])]
  have hroot : r ≤ ‖((root y 1 : (𝓞_ℂ_[p] : Type)) : ℂ_[p])‖ := by
    have h1 : ((Z.z 2 : (𝓞_ℂ_[p] : Type)) : ℂ_[p]) - 1 =
        ((root y 1 : (𝓞_ℂ_[p] : Type)) : ℂ_[p]) - ((root y 1 - (Z.z 2 - 1) : (𝓞_ℂ_[p] : Type)) : ℂ_[p]) := by
      push_cast; ring
    have h2 := IsUltrametricDist.norm_add_le_max ((root y 1 : (𝓞_ℂ_[p] : Type)) : ℂ_[p])
      (-((root y 1 - (Z.z 2 - 1) : (𝓞_ℂ_[p] : Type)) : ℂ_[p]))
    rw [norm_neg, ← sub_eq_add_neg, ← h1] at h2
    rcases le_max_iff.mp h2 with h | h
    · exact h
    · linarith
  have hy : ‖((y.untilt : (𝓞_ℂ_[p] : Type)) : ℂ_[p])‖ = ‖((root y 1 : (𝓞_ℂ_[p] : Type)) : ℂ_[p])‖ ^ p := by
    rw [← root_pow y 1, pow_one]; push_cast; rw [norm_pow]
  rw [map_pow]
  push_cast
  rw [norm_pow, hy, ← pow_mul]
  calc ‖(p : ℂ_[p])‖ ≤ r ^ (p * (p - 1)) := hr
    _ ≤ _ := pow_le_pow_left₀ (le_trans (norm_nonneg _) hrp.le) hroot _

/-- `p♭ = (ε^{1/p} - 1)^{p-1} · d` in `O♭`. -/
theorem pFlat_dvd : ∃ d, pFlat p = (eps1 Z - 1) ^ (p - 1) * d := by
  apply dvd_of_norm_le
  · intro h0
    have := norm_untilt_pow_ge Z
    rw [h0, norm_zero] at this
    linarith [norm_p_pos p]
  · rw [untilt_pFlat]
    exact norm_untilt_pow_ge Z


/-- `ω = Σ_{i<p} [ε^{1/p}]^i ∈ W(O♭)`. -/
def omega : (WittVector p (PreTilt (𝓞_ℂ_[p] : Type) p)) := ∑ i ∈ Finset.range p, teichmuller p (eps1 Z) ^ i

theorem theta_omega : fontaineTheta (𝓞_ℂ_[p] : Type) p (omega Z) = 0 := by
  rw [omega, map_sum]
  simp only [map_pow, fontaineTheta_teichmuller, untilt_eps1]
  exact sum_z1_eq_zero Z

/-- **`ker θ = (ω)`** in `W(O♭)` (Fontaine's generator `ω = ([ε] - 1)/([ε^{1/p}] - 1)`). -/
theorem ker_theta_eq_omega : RingHom.ker (fontaineTheta (𝓞_ℂ_[p] : Type) p) = span {omega Z} := by
  apply ker_eq_span_of_mod_p p (fontaineTheta (𝓞_ℂ_[p] : Type) p) (p_regular p) (omega Z) (theta_omega Z)
  intro x hx
  have hx' : x ∈ span {xi p} := by rw [← ker_fontaineTheta_Cp p]; exact hx
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx'
  obtain ⟨d, hd⟩ := pFlat_dvd Z
  have hmem : teichmuller p ((eps1 Z - 1) ^ (p - 1)) - omega Z ∈ span {(p : (WittVector p (PreTilt (𝓞_ℂ_[p] : Type) p)))} := by
    have hc : ∀ e : PreTilt (𝓞_ℂ_[p] : Type) p, constantCoeff (teichmuller p e) = e := fun e => by simp
    rw [← ker_constantCoeff, RingHom.mem_ker, map_sub, omega, map_sum, hc]
    simp only [map_pow, hc]
    rw [geom_eq (eps1 Z) (eps1_sub_one_ne_zero Z), sub_self]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨-(y * teichmuller p d), y - y * w * teichmuller p d, ?_⟩
  rw [xi, hd, map_mul]
  linear_combination (y * teichmuller p d) * hw

theorem xi_mem_span_omega : ∃ v, v * omega Z = xi p := by
  have : xi p ∈ span {omega Z} := by
    rw [← ker_theta_eq_omega Z, ker_fontaineTheta_Cp p]
    exact Ideal.mem_span_singleton_self _
  exact Ideal.mem_span_singleton'.mp this


/-! ## 5. In `B_dR^+`: `[ε] - 1 = ω · unit`, so `[ε] - 1 ∈ (ξ) \ (ξ²)` -/


variable (p) in
/-- The canonical ring map `W(O♭) → W(O♭)[1/p] → B_dR^+`. -/
def plus : (WittVector p (PreTilt (𝓞_ℂ_[p] : Type) p)) →+* (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) :=
  (algebraMap (Localization.Away (p : (WittVector p (PreTilt (𝓞_ℂ_[p] : Type) p))))
    (AdicCompletion (RingHom.ker (fontaineThetaInvertP (𝓞_ℂ_[p] : Type) p)) (Localization.Away (p : (WittVector p (PreTilt (𝓞_ℂ_[p] : Type) p)))))).comp
    (algebraMap (WittVector p (PreTilt (𝓞_ℂ_[p] : Type) p)) (Localization.Away (p : (WittVector p (PreTilt (𝓞_ℂ_[p] : Type) p)))))

theorem plus_apply (w : (WittVector p (PreTilt (𝓞_ℂ_[p] : Type) p))) :
    plus p w = ofPlus (𝓞_ℂ_[p] : Type) p (algebraMap (WittVector p (PreTilt (𝓞_ℂ_[p] : Type) p)) (Localization.Away (p : (WittVector p (PreTilt (𝓞_ℂ_[p] : Type) p)))) w) := rfl

theorem plus_xi : plus p (xi p) = ofPlus (𝓞_ℂ_[p] : Type) p (xi' p) := rfl

theorem thetaPlus_plus (w : (WittVector p (PreTilt (𝓞_ℂ_[p] : Type) p))) :
    thetaPlus p (plus p w) = algebraMap (𝓞_ℂ_[p] : Type) (Localization.Away (p : (𝓞_ℂ_[p] : Type))) (fontaineTheta (𝓞_ℂ_[p] : Type) p w) := by
  rw [plus_apply, thetaPlus_ofPlus, fontaineThetaInvertP, Localization.awayLift,
    IsLocalization.Away.lift_eq]
  rfl

theorem mem_max_iff (x : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) : x ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) ↔ thetaPlus p x = 0 := by
  rw [maximalIdeal_BDeRhamPlus, ← ker_thetaPlus, RingHom.mem_ker]

theorem plus_mem_max_iff (w : (WittVector p (PreTilt (𝓞_ℂ_[p] : Type) p))) :
    plus p w ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) ↔ fontaineTheta (𝓞_ℂ_[p] : Type) p w = 0 := by
  rw [mem_max_iff, thetaPlus_plus]
  exact map_eq_zero_iff _ (IsFractionRing.injective (𝓞_ℂ_[p] : Type) (Localization.Away (p : (𝓞_ℂ_[p] : Type))))

variable (p) in
/-- `ξ ∈ B_dR^+`. -/
abbrev varpi : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) := ofPlus (𝓞_ℂ_[p] : Type) p (xi' p)

theorem varpi_ne_zero : varpi p ≠ 0 := by simpa using ofPlus_xi'_pow_ne_zero p 1

theorem varpi_mem_max : varpi p ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) := by
  rw [maximalIdeal_BDeRhamPlus]; exact Ideal.mem_span_singleton_self _

theorem varpi_not_mem_sq : varpi p ∉ (span {varpi p ^ 2} : Ideal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) := by
  intro h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  have h1 : varpi p * (1 - varpi p * c) = 0 := by linear_combination -hc
  have h2 : varpi p * c = 1 :=
    (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left varpi_ne_zero)).symm
  exact (IsLocalRing.notMem_maximalIdeal.mpr (isUnit_iff_exists_inv.mpr ⟨c, h2⟩)) varpi_mem_max

theorem isUnit_u1 : IsUnit (plus p (teichmuller p (eps1 Z) - 1)) := by
  rw [← IsLocalRing.notMem_maximalIdeal, plus_mem_max_iff, map_sub, fontaineTheta_teichmuller,
    untilt_eps1, map_one]
  exact sub_ne_zero.mpr Z.one_ne

theorem plus_omega_mem : plus p (omega Z) ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) :=
  (plus_mem_max_iff _).mpr (theta_omega Z)

theorem plus_omega_not_mem_sq : plus p (omega Z) ∉ (span {varpi p ^ 2} : Ideal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) := by
  intro h
  obtain ⟨v, hv⟩ := xi_mem_span_omega Z
  apply varpi_not_mem_sq (p := p)
  show plus p (xi p) ∈ (span {varpi p ^ 2} : Ideal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p))
  rw [← hv, map_mul]
  exact Ideal.mul_mem_left _ _ h

/-- The variable of the logarithm, `[ε] - 1 ∈ B_dR^+`. -/
def xe : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) := plus p (teichmuller p (eps Z)) - 1

theorem xe_eq : xe Z = plus p (omega Z) * plus p (teichmuller p (eps1 Z) - 1) := by
  rw [xe, ← eps1_pow Z, map_pow, map_pow, omega, map_sum, map_sub, map_one]
  simp only [map_pow]
  rw [geom_sum_mul]

theorem xe_mem : xe Z ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) := by
  rw [xe_eq]; exact Ideal.mul_mem_right _ _ (plus_omega_mem Z)

theorem xe_not_mem_sq : xe Z ∉ (span {varpi p ^ 2} : Ideal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) := by
  intro h
  obtain ⟨u, hu⟩ := isUnit_u1 Z
  apply plus_omega_not_mem_sq Z
  have : plus p (omega Z) = xe Z * ↑u⁻¹ := by rw [xe_eq, ← hu, Units.mul_inv_cancel_right]
  rw [this]
  exact Ideal.mul_mem_right _ _ h

/-! ## 6. `t = log[ε] = Σ_{n ≥ 1} (-1)^{n+1} ([ε] - 1)^n / n` in `B_dR^+` -/

theorem isUnit_natCast (n : ℕ) (hn : n ≠ 0) : IsUnit (n : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) := by
  rw [← IsLocalRing.notMem_maximalIdeal, maximalIdeal_BDeRhamPlus, ← ker_thetaPlusCp,
    RingHom.mem_ker, map_natCast]
  exact Nat.cast_ne_zero.mpr hn

/-- The `n`-th term `(-1)^{n+1} xⁿ/n` of `log(1 + x)`. -/
def logTerm (x : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) (n : ℕ) : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) := (-1) ^ (n + 1) * Ring.inverse (n : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) * x ^ n

/-- The partial sum `Σ_{n=1}^{k} (-1)^{n+1} xⁿ/n`. -/
def logPartial (x : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) (k : ℕ) : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) := ∑ i ∈ Finset.range k, logTerm x (i + 1)

theorem logTerm_mem {x : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)} (hx : x ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) (n : ℕ) :
    logTerm x n ∈ (span {varpi p} : Ideal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) ^ n := by
  rw [maximalIdeal_BDeRhamPlus] at hx
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hx n)

theorem smul_top_eq (n : ℕ) :
    ((span {varpi p} : Ideal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) ^ n • ⊤ : Submodule (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) = (span {varpi p} : Ideal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) ^ n := by
  rw [smul_eq_mul, Ideal.mul_top]

theorem logPartial_cauchy {x : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)} (hx : x ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) {m n : ℕ} (h : m ≤ n) :
    logPartial x m ≡ logPartial x n [SMOD ((span {varpi p} : Ideal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) ^ m • ⊤ : Submodule (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) (BDeRhamPlus (𝓞_ℂ_[p] : Type) p))] := by
  rw [SModEq.sub_mem, smul_top_eq, logPartial, logPartial, Finset.range_eq_Ico, Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le m) h, sub_add_cancel_left]
  refine neg_mem (Ideal.sum_mem _ fun i hi => ?_)
  exact Ideal.pow_le_pow_right (by have := (Finset.mem_Ico.mp hi).1; omega) (logTerm_mem hx (i + 1))

variable (p) in
/-- **`log(1 + x)`** for `x` in the maximal ideal `(ξ)` of `B_dR^+`: the `ξ`-adic limit of the partial sums
(it exists because `B_dR^+` is `ξ`-adically complete, bdr-kertheta). -/
def logPlus (x : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) (hx : x ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) :=
  Classical.choose (IsPrecomplete.prec (I := (span {varpi p} : Ideal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p))) inferInstance
    (fun h => logPartial_cauchy hx h))

theorem logPlus_spec (x : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) (hx : x ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) (n : ℕ) :
    logPartial x n ≡ logPlus p x hx [SMOD ((span {varpi p} : Ideal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) ^ n • ⊤ : Submodule (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) (BDeRhamPlus (𝓞_ℂ_[p] : Type) p))] :=
  Classical.choose_spec (IsPrecomplete.prec (I := (span {varpi p} : Ideal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p))) inferInstance
    (fun h => logPartial_cauchy hx h)) n

/-- The limit is unique (`B_dR^+` is `ξ`-adically separated), so `logPlus` is *the* sum of the series. -/
theorem logPlus_unique (x : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) (hx : x ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) (L : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p))
    (hL : ∀ n, logPartial x n ≡ L [SMOD ((span {varpi p} : Ideal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) ^ n • ⊤ : Submodule (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) (BDeRhamPlus (𝓞_ℂ_[p] : Type) p))]) :
    L = logPlus p x hx := by
  rw [IsHausdorff.eq_iff_smodEq (I := (span {varpi p} : Ideal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)))]
  intro n
  exact (hL n).symm.trans (logPlus_spec x hx n)

theorem logPlus_sub_mem (x : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) (hx : x ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) :
    logPlus p x hx - x ∈ (span {varpi p ^ 2} : Ideal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) := by
  have h2 := logPlus_spec x hx 2
  rw [SModEq.sub_mem, smul_top_eq] at h2
  have hp2 : logPartial x 2 = x + logTerm x 2 := by
    simp [logPartial, logTerm, Finset.sum_range_succ, one_add_one_eq_two]
  have h3 := logTerm_mem (p := p) hx 2
  rw [← Ideal.span_singleton_pow]
  have : logPlus p x hx - x = -(logPartial x 2 - logPlus p x hx) + logTerm x 2 := by
    rw [hp2]; ring
  rw [this]
  exact Ideal.add_mem _ (neg_mem h2) h3

variable (p) in
/-- **Fontaine's `t = log[ε]`** in the kernel's `B_dR^+`. -/
def tt : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) := logPlus p (xe Z) (xe_mem Z)

theorem tt_mem : tt p Z ∈ IsLocalRing.maximalIdeal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) := by
  have h := logPlus_sub_mem (xe Z) (xe_mem Z)
  have h1 : (span {varpi p ^ 2} : Ideal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) ≤ IsLocalRing.maximalIdeal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.pow_mem_of_mem _ varpi_mem_max 2 (by norm_num)
  have : tt p Z = xe Z + (tt p Z - xe Z) := by ring
  rw [this]
  exact Ideal.add_mem _ (xe_mem Z) (h1 h)

theorem tt_not_mem_sq : tt p Z ∉ (span {varpi p ^ 2} : Ideal (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) := by
  intro h
  apply xe_not_mem_sq Z
  have h1 := logPlus_sub_mem (xe Z) (xe_mem Z)
  have : xe Z = tt p Z - (tt p Z - xe Z) := by ring
  rw [this]
  exact Ideal.sub_mem _ h h1

theorem tt_ne_zero : tt p Z ≠ 0 := fun h => tt_not_mem_sq Z (h ▸ Ideal.zero_mem _)

/-- **`t = ξ · unit`** in `B_dR^+`. -/
theorem tt_eq_varpi_mul_unit : ∃ u : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p), IsUnit u ∧ tt p Z = varpi p * u := by
  obtain ⟨n, u, hu, h⟩ := eq_xi_pow_mul_unit p (tt p Z) (tt_ne_zero Z)
  rcases n with _ | _ | n
  · exfalso
    rw [pow_zero, one_mul] at h
    exact (IsLocalRing.notMem_maximalIdeal.mpr hu) (h ▸ tt_mem Z)
  · exact ⟨u, hu, by rw [h, zero_add, pow_one]⟩
  · exfalso
    apply tt_not_mem_sq Z
    rw [h, Ideal.mem_span_singleton']
    exact ⟨varpi p ^ n * u, by ring⟩

/-! ## 7. The dictionary `B_dR ≅ B_dR^+[1/t]` -/

theorem isFractionRing_away_tt : IsFractionRing (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) (Localization.Away (tt p Z)) := by
  obtain ⟨u, hu, htu⟩ := tt_eq_varpi_mul_unit Z
  refine IsLocalization.of_le_of_exists_dvd (Submonoid.powers (tt p Z)) (nonZeroDivisors _)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (tt_ne_zero Z)) ?_
  intro n hn
  obtain ⟨k, v, hv, rfl⟩ := eq_xi_pow_mul_unit p n (nonZeroDivisors.ne_zero hn)
  refine ⟨tt p Z ^ k, ⟨k, rfl⟩, ?_⟩
  rw [htu, mul_pow]
  exact mul_dvd_mul_left _ hv.dvd

/-- **`B_dR(𝓞_ℂ_p) ≅ B_dR^+[1/t]`**, `t = log[ε]`, as `B_dR^+`-algebras: a print that defines
`B_dR = B_dR^+[1/t]` (Berger) defines the kernel's `B_dR` up to a canonical isomorphism over `B_dR^+`. -/
def bdREquivAwayT : BdR (𝓞_ℂ_[p] : Type) p ≃ₐ[(BDeRhamPlus (𝓞_ℂ_[p] : Type) p)] Localization.Away (tt p Z) :=
  haveI := isFractionRing_away_tt Z
  haveI := isFractionRing_BDeRham p
  IsLocalization.algEquiv (nonZeroDivisors (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)) (BdR (𝓞_ℂ_[p] : Type) p) (Localization.Away (tt p Z))


/-- **The `G_{ℚ_p}`-action on `B_dR^+[1/t]` is determined by the action on `B_dR^+`**: two ring endomorphisms of
`B_dR^+[1/t]` extending the same `g : B_dR^+ → B_dR^+` are equal. So the print's action on `B_dR^+[1/t]` (the
extension of the action on `B_dR^+`) is the transport of any extension on the kernel's `B_dR`, e.g. `bdrAct`
(`transport_extends`). -/
theorem ext_of_extends {g : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) →+* (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)} (f₁ f₂ : Localization.Away (tt p Z) →+* Localization.Away (tt p Z))
    (h₁ : f₁.comp (algebraMap (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) _) = (algebraMap (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) _).comp g)
    (h₂ : f₂.comp (algebraMap (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) _) = (algebraMap (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) _).comp g) : f₁ = f₂ :=
  IsLocalization.ringHom_ext (Submonoid.powers (tt p Z)) (h₁.trans h₂.symm)

/-- The transport of an extension `φ` of `g` to `B_dR` along `bdREquivAwayT` extends `g` on `B_dR^+[1/t]`. -/
theorem transport_extends {g : (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) →+* (BDeRhamPlus (𝓞_ℂ_[p] : Type) p)} (φ : BdR (𝓞_ℂ_[p] : Type) p →+* BdR (𝓞_ℂ_[p] : Type) p)
    (hφ : φ.comp (algebraMap (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) (BdR (𝓞_ℂ_[p] : Type) p)) = (algebraMap (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) (BdR (𝓞_ℂ_[p] : Type) p)).comp g) :
    (((bdREquivAwayT Z).toRingEquiv.toRingHom.comp φ).comp
      (bdREquivAwayT Z).symm.toRingEquiv.toRingHom).comp (algebraMap (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) _) =
      (algebraMap (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) _).comp g := by
  ext x
  simp only [RingHom.comp_apply]
  have h1 : (bdREquivAwayT Z).symm.toRingEquiv.toRingHom (algebraMap (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) _ x) = algebraMap (BDeRhamPlus (𝓞_ℂ_[p] : Type) p) (BdR (𝓞_ℂ_[p] : Type) p) x :=
    (bdREquivAwayT Z).symm.commutes x
  rw [h1]
  have h2 := congrArg (fun f => f x) hφ
  simp only [RingHom.comp_apply] at h2
  rw [h2]
  exact (bdREquivAwayT Z).commutes (g x)

/-! ## 8. Such systems exist -/

variable (p) in
theorem exists_primitiveRoot : ∃ ζ : ℂ_[p], IsPrimitiveRoot ζ p := by
  have : NeZero (p : ℂ_[p]) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p ℂ_[p])
    (Polynomial.degree_cyclotomic_pos p ℂ_[p] hp.out.pos).ne'
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

variable (p) in
/-- `1, ζ_p, ζ_{p²}, …` in `ℂ_p`. -/
def zetaSeq : ℕ → ℂ_[p]
  | 0 => 1
  | 1 => Classical.choose (exists_primitiveRoot p)
  | n + 2 => Classical.choose (IsAlgClosed.exists_pow_nat_eq (zetaSeq (n + 1)) hp.out.pos)

theorem zetaSeq_succ_pow (n : ℕ) : zetaSeq p (n + 1) ^ p = zetaSeq p n := by
  rcases n with _ | n
  · exact (Classical.choose_spec (exists_primitiveRoot p)).pow_eq_one
  · exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (zetaSeq p (n + 1)) hp.out.pos)

theorem zetaSeq_mem (n : ℕ) : zetaSeq p n ∈ 𝓞_ℂ_[p] := by
  have h : zetaSeq p n ^ p ^ n = 1 := by
    induction n with
    | zero => simp [zetaSeq]
    | succ n ih => rw [pow_succ', pow_mul, zetaSeq_succ_pow, ih]
  rw [mem_O_iff]
  have h1 : ‖zetaSeq p n‖ ^ p ^ n = 1 := by rw [← norm_pow, h, norm_one]
  have h2 : ‖zetaSeq p n‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.out.ne_zero)).mp h1
  exact h2.le

variable (p) in
/-- **A compatible system of `p`-power roots of unity exists** (so `RootSystem p` is inhabited and the
hypotheses of §§4-7 are satisfiable). -/
def rootSystem : RootSystem p where
  z n := ⟨zetaSeq p n, zetaSeq_mem n⟩
  pow_succ n := Subtype.ext (by push_cast; exact zetaSeq_succ_pow n)
  zero := Subtype.ext rfl
  one_ne h := by
    have h1 := congrArg Subtype.val h
    exact (Classical.choose_spec (exists_primitiveRoot p)).ne_one hp.out.one_lt h1

end

end DeRhamPrint.TDict
