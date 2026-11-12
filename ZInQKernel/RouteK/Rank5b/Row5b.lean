import ZInQKernel.RouteK.Rank5b.Kernel

/-!
# Route K, row 5b: Lemma 4.1 for `Sel₂(C_n)`, Theorem 4.3, Corollary 4.4 and `CertifiedRank5b`

`docs/research/tyz-5b.md` §4, for squarefree `n ≡ 5 (mod 8)`:

* `sel2_ncard_eq_four_mul`: `#Sel₂(C_n) = 4 · #ker M₁` (Lemma 4.1, through Proposition 0 and
  `selPair_injective`); `sel2HEquivKer`: `H ≅ ker M₁` by `(a, b) ↦ (u + v, u)`;
* `det_M5b_eq_dot` (Theorem 4.3): if `#Sel₂ = 8`, then `det M_5b = y·u` for any non-torsion class;
* `det_M5b_eq_one` (Corollary 4.4, first sentence): if moreover some `(a, b) ∈ Sel₂` has
  `|a| ≡ 7 (mod 8)`, then `det M_5b = 1`;
* `CertifiedRank5b`, the hypothesis in Smith's row-5b form, and
  `certifiedRankSel_of_certifiedRank5b : CertifiedRank5b → Selmer.CertifiedRankSel`.
-/

namespace ZInQ.RouteK.Rank5b

open Matrix Selmer

/-! ### Theorem 4.3 on a configuration -/

namespace Config

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (𝒞 : RouteK.Config ι)

omit [DecidableEq ι] in
theorem ofKer_zero : ofKer 𝒞 0 = tors 0 0 := by
  ext <;> simp [ofKer, tors, dot]

omit [Fintype ι] [DecidableEq ι] in
theorem uadd_tors_zero_zero (e f : ZMod 2) : uadd (tors (ι := ι) 0 0) (tors e f) = tors e f := by
  ext <;> simp [uadd, tors]

/-- **Theorem 4.3 on a configuration.** For a configuration of product class `5` whose system has
exactly 8 solutions, `det M_5b = λ·u` for every non-torsion solution `σ`. -/
theorem det_M5bc_eq (h5 : 𝒞.prodClass = 5) (h8 : 𝒞.sols.card = 8) {σ : Unknowns ι}
    (hσ : 𝒞.IsSol σ) (hnt : ∀ e f, σ ≠ tors e f) : (M5bc 𝒞).det = dot 𝒞.lam σ.u := by
  have hl := lam_sum_of_five 𝒞 h5
  have hcard : Fintype.card {w // M1c 𝒞 *ᵥ w = 0} = 2 := by
    have := card_sols_eq 𝒞 h5; omega
  set c := torsCoord 𝒞 σ
  set h := uadd σ (tors c.1 c.2) with hh
  have hH : IsH 𝒞 h := isH_uadd_torsCoord 𝒞 h5 hσ
  have hk := M1c_mulVec_kvec 𝒞 h5 hH
  have hk0 : kvec h ≠ 0 := by
    intro h0
    have h1 := ofKer_kvec 𝒞 hH
    rw [h0, ofKer_zero] at h1
    apply hnt c.1 c.2
    rw [← uadd_tors_tors σ c.1 c.2, ← hh, ← h1, uadd_tors_zero_zero]
  have hker : ∀ w, M1c 𝒞 *ᵥ w = 0 → w = 0 ∨ w = kvec h := by
    intro w hw
    by_contra hne
    rw [not_or] at hne
    have h3 : 2 < Fintype.card {w // M1c 𝒞 *ᵥ w = 0} := by
      rw [Fintype.two_lt_card_iff]
      refine ⟨⟨0, mulVec_zero _⟩, ⟨kvec h, hk⟩, ⟨w, hw⟩, ?_, ?_, ?_⟩
      · intro e; exact hk0 (congrArg Subtype.val e).symm
      · intro e; exact hne.1 (congrArg Subtype.val e).symm
      · intro e; exact hne.2 (congrArg Subtype.val e).symm
    omega
  rw [M5bc, det_border_eq_dotProduct (M1c 𝒞) (M1c_transpose 𝒞) (kvec h) hk0 hk hker]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    zero_mul, Finset.sum_const_zero, zero_add, kvec]
  have : dot 𝒞.lam h.u = dot 𝒞.lam σ.u := by
    simp only [hh, uadd, tors, dot_add_right, dot_const, hl, mul_zero, add_zero]
  exact this

end Config

/-! ### Lemma 4.1 for `Sel₂(C_n)` -/

section nat

variable {d : ℕ}

theorem sel2_eq_image (hd5 : d % 8 = 5) (hsq : Squarefree d) :
    Sel2 d = selPair d '' ↑(natConfig d (odd_of_mod_eight_eq_five hd5)).sols := by
  ext ab
  constructor
  · intro hab
    obtain ⟨σ, rfl⟩ := sel2_subset_range_selPair (odd_of_mod_eight_eq_five hd5) hab
    exact ⟨σ, by rw [Finset.mem_coe, RouteK.Config.mem_sols, prop0 hd5 hsq]; exact hab, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩
    rw [Finset.mem_coe, RouteK.Config.mem_sols, prop0 hd5 hsq] at hσ
    exact hσ

/-- `#Sel₂(C_n) = #Σ(𝒞_n)`, by Proposition 0 and `selPair_injective`. -/
theorem sel2_ncard_eq_card_sols (hd5 : d % 8 = 5) (hsq : Squarefree d) :
    (Sel2 d).ncard = (natConfig d (odd_of_mod_eight_eq_five hd5)).sols.card := by
  rw [sel2_eq_image hd5 hsq,
    Set.ncard_image_of_injective _ (selPair_injective (odd_of_mod_eight_eq_five hd5)),
    Set.ncard_coe_finset]

/-- **Lemma 4.1, the count** (tyz-5b §4.1). For squarefree `n ≡ 5 (mod 8)`,
`#Sel₂(C_n) = 4 · #ker M₁`, i.e. `dim Sel₂(C_n) = 2 + corank M₁`. -/
theorem sel2_ncard_eq_four_mul (hd5 : d % 8 = 5) (hsq : Squarefree d) :
    (Sel2 d).ncard = 4 * Fintype.card {w // M1 d *ᵥ w = 0} := by
  have hd := odd_of_mod_eight_eq_five hd5
  have h5 : (natConfig d hd).prodClass = 5 := by
    rw [natConfig_prodClass hd hsq, natCast_zmod8_of_mod hd5]; rfl
  rw [sel2_ncard_eq_card_sols hd5 hsq, Config.card_sols_eq _ h5, M1_eq_M1c hd]

/-- **Lemma 4.1, the isomorphism** (tyz-5b §4.1). For squarefree `n ≡ 5 (mod 8)`, the Selmer
classes `(a, b) = selPair n σ` with `b₁ = 0` (`b` odd) and `a₀ = y·u` (`a ≡ 1 (mod 4)`) form the
subspace `H`, and `σ ↦ (u + v, u)` is a bijection from `H` onto `ker M₁`. -/
noncomputable def sel2HEquivKer (hd5 : d % 8 = 5) (hsq : Squarefree d) :
    {σ : Unknowns d.primeFactors //
      selPair d σ ∈ Sel2 d ∧ σ.b1 = 0 ∧ σ.a0 = dot (yBit d) σ.u} ≃
      {w // M1 d *ᵥ w = 0} := by
  have hd := odd_of_mod_eight_eq_five hd5
  have h5 : (natConfig d hd).prodClass = 5 := by
    rw [natConfig_prodClass hd hsq, natCast_zmod8_of_mod hd5]; rfl
  have hy : (natConfig d hd).lam = yBit d := funext (natConfig_lam_eq_yBit hd)
  refine (Equiv.subtypeEquivRight fun σ => ?_).trans
    ((Config.hEquivKer _ h5).trans (Equiv.subtypeEquivRight fun w => ?_))
  · rw [Config.IsH, prop0 hd5 hsq, hy]
  · rw [M1_eq_M1c hd]

theorem sel2HEquivKer_apply (hd5 : d % 8 = 5) (hsq : Squarefree d) (σ) :
    (sel2HEquivKer hd5 hsq σ).1 = Sum.elim (σ.1.u + σ.1.v) σ.1.u := rfl

/-! ### Theorem 4.3 and Corollary 4.4 -/

/-- **Theorem 4.3** (rule of row 5b, tyz-5b §4.2). Let `n ≡ 5 (mod 8)` be squarefree with
`#Sel₂(C_n) = 8`, and let `(a, b) = selPair n σ ∈ Sel₂(C_n)` be a non-torsion class (`σ` is not one
of the four torsion classes `tors e f`). Then `det M_5b = y·u = Σ_{p ∣ a} y_p`. -/
theorem det_M5b_eq_dot (hd5 : d % 8 = 5) (hsq : Squarefree d) (h8 : (Sel2 d).ncard = 8)
    {σ : Unknowns d.primeFactors} (hσ : selPair d σ ∈ Sel2 d) (hnt : ∀ e f, σ ≠ tors e f) :
    (M5b d).det = dot (yBit d) σ.u := by
  have hd := odd_of_mod_eight_eq_five hd5
  have h5 : (natConfig d hd).prodClass = 5 := by
    rw [natConfig_prodClass hd hsq, natCast_zmod8_of_mod hd5]; rfl
  have hy : (natConfig d hd).lam = yBit d := funext (natConfig_lam_eq_yBit hd)
  rw [sel2_ncard_eq_card_sols hd5 hsq] at h8
  rw [M5b_eq_M5bc hd, Config.det_M5bc_eq _ h5 h8 ((prop0 hd5 hsq σ).2 hσ) hnt, hy]

/-- The absolute value of `classInt n e₀ 0 w` is `Π_{p ∣ n} p^{w_p}`. -/
theorem natAbs_classInt_zero (e₀ : ZMod 2) (w : d.primeFactors → ZMod 2) :
    (classInt d e₀ 0 w).natAbs = ∏ p : d.primeFactors, (p : ℕ) ^ (w p).val := by
  simp only [classInt, ZMod.val_zero, pow_zero, mul_one, Int.natAbs_mul, Int.natAbs_pow,
    Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul]
  rw [← Int.natAbsHom_apply, map_prod]
  simp [Int.natAbs_pow]

/-- The class of `Π_{p ∣ n} p^{w_p}` mod 4 is `y·w`: `λ` of its class mod 8 is `Σ y_p w_p`. -/
theorem lam8_prod_pow (hd : Odd d) (w : d.primeFactors → ZMod 2) :
    lam8 ((∏ p : d.primeFactors, (p : ℕ) ^ (w p).val : ℕ) : ZMod 8) = dot (yBit d) w := by
  have hmem : ∀ q : d.primeFactors, ((q : ℕ) : ZMod 8) ∈ oddClasses := fun q =>
    natCast_mem_oddClasses (odd_prime_of_mem_primeFactors hd q)
  push_cast
  rw [lam8_prod _ _ fun q _ => oddClasses_pow (hmem q) _]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [lam8_pow (hmem q), ZMod.natCast_zmod_val, mul_comm, ← natConfig_lam_eq_lam8 hd,
    natConfig_lam_eq_yBit hd]

/-- **Corollary 4.4, first sentence** (tyz-5b §4.2). Let `n ≡ 5 (mod 8)` be squarefree with
`#Sel₂(C_n) = 8`. If some `(a, b) ∈ Sel₂(C_n)` has `|a| ≡ 7 (mod 8)`, then `det M_5b = 1`. -/
theorem det_M5b_eq_one (hd5 : d % 8 = 5) (hsq : Squarefree d) (h8 : (Sel2 d).ncard = 8)
    {ab : ℤ × ℤ} (hab : ab ∈ Sel2 d) (h7 : ab.1.natAbs % 8 = 7) : (M5b d).det = 1 := by
  have hd := odd_of_mod_eight_eq_five hd5
  obtain ⟨σ, rfl⟩ := sel2_subset_range_selPair hd hab
  have hsol := (prop0 hd5 hsq σ).2 hab
  have ha1 := RouteK.Config.IsSol.a1_eq_zero _ hsol
  have habs : (selPair d σ).1.natAbs = ∏ p : d.primeFactors, (p : ℕ) ^ (σ.u p).val := by
    rw [selPair, ha1, natAbs_classInt_zero]
  rw [habs] at h7
  have hlam : dot (yBit d) σ.u = 1 := by
    rw [← lam8_prod_pow hd, natCast_zmod8_of_mod h7]; decide
  rw [det_M5b_eq_dot hd5 hsq h8 hab ?_, hlam]
  rintro e f rfl
  simp only [tors] at h7
  rcases zmod2_eq_zero_or_one' f with rfl | rfl
  · simp at h7
  · simp only [show (1 : ZMod 2).val = 1 from rfl, pow_one] at h7
    rw [Finset.prod_coe_sort d.primeFactors (fun p : ℕ => p),
      Nat.prod_primeFactors_of_squarefree hsq] at h7
    omega

end nat

/-! ### The hypothesis in Smith's row-5b form -/

/-- **Hypothesis CR₃^5b** (tyz-5b §1 and §3). Let `n > 0` be squarefree with `n ≡ 5 (mod 8)`. If
`#Sel₂(C_n) = 8` and the determinant of Smith's row-5b matrix `M_5b` (`M5b n`, built from the
Legendre symbols of the primes of `n`) is `1`, then the 2-covering `D_{a,b}` of every
`(a, b) ∈ Sel₂(C_n)` has a rational point.

**Trust statement.** CR₃^5b is not proved in Lean. Lean derives it from
`Rank.CertifiedRankTYZClRk` (through `CertifiedRankTYZ` and `certifiedRank5b_of_certifiedRankTYZ`;
see `docs/research/cr3-trust.md`). It follows from Tian–Yuan–Zhang
(Y. Tian, X. Yuan, S.-W. Zhang, *Genus periods, genus points and congruent number problem*, Asian
J. Math. 21 (2017), no. 4, 721–774: Theorem 3.5 and the argument of the proof of Theorem 3.5(2) in
§3.3, as completed in `docs/research/nt-tyz.md` §4, Proposition N, through Smith's row 5b)
together with Gross–Zagier with an auxiliary imaginary quadratic field, as follows
(`docs/research/tyz-5b.md` §§1, 3):

* tyz-5b §3 (elementary, Smith's row 5b reproved): `det M_5b = T_5b(n)`, the genus sum
  `Σ_{d₀ ≡ 7, d₁ ≡ 3 (8)} g(d₀)g(d₁)𝓛(n/d₀d₁)` mod 2, with `g(d) = #2Cl(ℚ(√−d)) mod 2`;
* tyz-5b §1.2 (TYZ, proof of Theorem 3.5(2)): if `T_5b(n)` is odd then `2^{−ρ(n)}𝓛(n)` is odd, so
  `𝓛(n) ≠ 0` and `ord_{s=1} L(C_n, s) = 1` (the root number is `−1` for `n ≡ 5 (mod 8)`);
* Gross–Zagier (Invent. Math. 84 (1986)), over an imaginary quadratic field with the Heegner
  hypothesis and `L(C_n^K, 1) ≠ 0` (Bump–Friedberg–Hoffstein): `rank C_n(ℚ) ≥ 1`; Kolyvagin's
  published papers enter only inside Tian–Yuan–Zhang, and the manuscript's Lemma 5.5 is not used;
* then `dim C_n(ℚ)/2C_n(ℚ) = 2 + rank ≥ 3 = dim Sel₂(C_n)`, so the Kummer map is onto `Sel₂(C_n)`
  and every Selmer class comes from a rational point, i.e. `D_{a,b}(ℚ) ≠ ∅`
  (`Selmer.loc_iff_kummer` over `ℚ`).

Only the step through Smith's matrix differs from `Selmer.CertifiedRankSel`: the 2-adic condition
"some `(a, b) ∈ Sel₂` has `|a| ≡ 7 (mod 8)`" is replaced by `det M_5b = 1`, which it implies
(`det_M5b_eq_one`, tyz-5b Corollary 4.4), so `CertifiedRank5b` implies `CertifiedRankSel`
(`certifiedRankSel_of_certifiedRank5b`). -/
def CertifiedRank5b : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → (Sel2 d).ncard = 8 → (M5b d).det = 1 →
    ∀ ab ∈ Sel2 d, Loc ℚ d ab.1 ab.2

/-- **CR₃^Sel from CR₃^5b**, by Corollary 4.4 (`det_M5b_eq_one`). -/
theorem certifiedRankSel_of_certifiedRank5b (h : CertifiedRank5b) : CertifiedRankSel :=
  fun d hd5 hsq h8 ⟨_, hab, h7⟩ => h d hd5 hsq h8 (det_M5b_eq_one hd5 hsq h8 hab h7)

end ZInQ.RouteK.Rank5b
