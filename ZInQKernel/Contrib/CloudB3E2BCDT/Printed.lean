import ZInQKernel.Contrib.OneProof.PoleS12.Leaves
import ZInQKernel.Contrib.CloudB3RC53.Hasse.Convergence
import ZInQKernel.Contrib.CloudB3RC53.WeilIsogeny.HasseProof
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.HeckeSlash.Recurrence
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.TrivialNebentypus
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.LFunction.Basic
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Breuil–Conrad–Diamond–Taylor, Theorem A, with the Introduction's condition (2), as printed

The headline hypothesis `ZInQ.Manuscript.PoleS12.BCDTThmA` asks, for every elliptic curve `E/ℚ`,
for a weight-2 cusp form on `Γ₀(N)` whose `q`-expansion coefficients are the Dirichlet
coefficients of Mathlib's `L(E, s)`. This file states the theorem the manuscript cites
(`\cite[Theorem A]{bcdt}`, tex L1092) in the form its authors print it, and proves the
headline hypothesis from that statement.

**The print.** C. Breuil, B. Conrad, F. Diamond, R. Taylor, *On the modularity of elliptic
curves over `ℚ`: wild 3-adic exercises*, J. Amer. Math. Soc. 14 (2001) 843–939. Read (AI) in
the authors' manuscript, Introduction, pp. 1–3:

* p. 1: "**Theorem A.** If `E/ℚ` is an elliptic curve, then `E` is modular."
* p. 1: `Γ₁(N)` is the group of matrices of `SL₂(ℤ)` congruent to `(1 ∗; 0 1)` modulo `N`;
  "a cusp form of weight `k ≥ 1` and level `N ≥ 1` is a holomorphic function `f` on the upper
  half complex plane" with `f((az + b)/(cz + d)) = (cz + d)^k f(z)` for `(a b; c d) ∈ Γ₁(N)` and
  `|f(z)|²(Im z)^k` bounded; `S_k(N)` is the space of them; `f(z) = ∑_{n ≥ 1} c_n(f) e^{2πinz}`
  and "we define the L-series of `f` to be `L(f, s) = ∑_{n ≥ 1} c_n(f)/n^s`".
* p. 2: "For each prime `p ∤ N` there is a linear operator `T_p` on `S_k(N)` defined by
  `(f|T_p)(z) = p^{-1} ∑_{i=0}^{p-1} f((z + i)/p) + p^{k-1}(cpz + d)^{-k} f((apz + b)/(cpz + d))`
  for any `(a b; c d) ∈ SL₂(ℤ)` with `c ≡ 0 mod N` and `d ≡ p mod N`. The operators `T_p` for
  `p ∤ N` can be simultaneously diagonalised on the space `S_k(N)` and a simultaneous
  eigenvector is called an *eigenform*."
* pp. 2–3: "Let `N(E)` denote the conductor of `E`. It is known that the following conditions
  are equivalent. … (2) The L-function `L(E, s)` of `E` equals the L-function `L(f, s)` for
  some eigenform `f` of weight 2 and level `N(E)`. … When these equivalent conditions are
  satisfied we call `E` modular."

Theorem A therefore asserts condition (2) for every `E/ℚ`. Note what an eigenform is in this
print: an eigenvector of the `T_p` for `p ∤ N` only. It is not assumed to be an eigenvector of
the diamond operators, nor normalized; no nebentypus is attached to it.

**The Lean statement** (`BCDTThmAPrinted`), over genuine definitions:
* `S_k(N)` is Mathlib's `CuspForm ((Gamma1 N).map (mapGL ℝ)) k` (holomorphic, weight-`k`
  invariant under `Γ₁(N)`, vanishing at every cusp; for holomorphic invariant `f` this is
  equivalent to the boundedness of `|f(z)|²(Im z)^k` printed on p. 1);
* `T_p` is Tau Ceti's `HeckeRing.GL2.heckeTCuspNat k p`, the slash operator of the double coset
  `Γ₁(N) diag(1, p) Γ₁(N)`; Tau Ceti decomposes it as
  `T_p f = ∑_{b < p} f ∣[k] (1 b; 0 p) + (⟨p⟩ f) ∣[k] (p 0; 0 1)`, which is the printed formula
  term by term (`∣[k] (1 b; 0 p)` is `p^{-1} f((z + b)/p)`, and `⟨p⟩ f` is slashing by the printed
  matrix `(a b; c d)`);
* an eigenform (`IsBCDTEigenform`) is a nonzero `f` with `T_p f ∈ ℂ f` for every prime `p ∤ N`
  ("eigenvector" includes `f ≠ 0`; with the `L`-function condition below this is automatic,
  since `c_1(f) = 1`);
* `c_n(f)` is the `n`-th coefficient of the `q`-expansion of width 1 (`q = e^{2πiz}`), and
  `L(f, s)` is Mathlib's `LSeries` of these coefficients;
* `L(E, s)` is Mathlib's `WeierstrassCurve.LSeries` (the Euler product over the minimal models,
  `1 - a_p T + p T²` at good `p`, `1 ∓ T` at multiplicative `p`, `1` at additive `p`);
* "`L(E, s)` equals `L(f, s)`" (`LFunctionsAgree`) is read as equality on a right half-plane,
  the weakest reading: both are Dirichlet series, and agreement on a half-plane determines them.

**Departure: the level.** Neither Mathlib nor the tree defines the conductor `N(E)` of an
elliptic curve over `ℚ`. `BCDTThmAPrinted` therefore says "of weight 2 and some level `N ≥ 1`":
condition (2) with `N(E)` weakened to an unspecified level. This is a consequence of the print
(take `N = N(E)`), never stronger. For whoever later defines the conductor, the statement with
the level given by a function `level : WeierstrassCurve ℚ → ℕ` is `BCDTThmAPrintedAtLevel level`,
and `bcdtThmAPrinted_of_atLevel` reduces it to `BCDTThmAPrinted`; the proof below uses nothing
about the level.

**The proof** (`bcdtThmA_of_printed : BCDTThmAPrinted → PoleS12.BCDTThmA`), PROVED:
1. `L(E, s)` converges absolutely on `Re s > 3/2` (Hasse's bound, proved in the tree:
   `hasseConvergence_proof`, `hasseBoundProved_proof`) and `L(f, s)` on `Re s > 2` (Hecke's
   bound, Tau Ceti's `CuspForm.abscissaOfAbsConv_qExpansion_coeff_le`), so Mathlib's uniqueness
   theorem for Dirichlet series (`LSeries.eq_of_LSeries_eventually_eq`) gives
   `c_n(f) = a_n(E)` for every `n ≥ 1`.
2. At a prime `p ∤ N`, Tau Ceti's recurrence `a_m(T_p f) = c_{pm}(f) + p c_{m/p}(⟨p⟩ f)` with
   `T_p f = λ f`, `λ = c_p(f)`, and the Euler factor `1 - a T + b T²` of `E` at `p`
   (`b = p` or `b = 0`) give `p ⟨p⟩ f = b f`. Since `⟨p⟩` is invertible and `f ≠ 0`, `b = p` and
   `⟨p⟩ f = f`. (So in particular `E` has good reduction at every prime not dividing the level.)
3. Dirichlet's theorem on primes in arithmetic progressions (Mathlib's
   `Nat.forall_exists_prime_gt_and_eq_mod`) gives `⟨d⟩ f = f` for every `d ∈ (ℤ/N)ˣ`, i.e. `f`
   has trivial nebentypus (`TauCeti.mem_cuspFormCharSpace_one_iff_diamondOpCusp`), and Tau
   Ceti's `cuspFormCharSpaceOneEquiv` reads it as a cusp form on `Γ₀(N)` with the same function.

**Classification.** `BCDTThmAPrinted`: PRINT (Theorem A with condition (2), consequence form in
one respect only: the level `N(E)` is weakened to some level `N`); read (AI) from the author
manuscript pp. 1–3, not yet checked against the journal pages. `bcdtThmA_of_printed`: PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3E2.BCDT

open LSeries Matrix.SpecialLinearGroup CongruenceSubgroup UpperHalfPlane HeckeRing.GL2 Polynomial WeierstrassCurve
  IsDedekindDomain Rat.HeightOneSpectrum

/-! ### The print -/

/-- **BCDT's eigenform** (author manuscript p. 2): a cusp form `f ∈ S_k(N)` on `Γ₁(N)` that is a
simultaneous eigenvector of the Hecke operators `T_p` for the primes `p ∤ N` (nonzero, as an
eigenvector is). No diamond-operator condition and no normalization. -/
def IsBCDTEigenform {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    Prop :=
  f ≠ 0 ∧ ∀ (p : ℕ) [NeZero p], p.Prime → ¬ p ∣ N → ∃ a : ℂ, heckeTCuspNat k p f = a • f

/-- The Fourier coefficients `c_n(f)` of `f(z) = ∑ c_n(f) e^{2πinz}` (author manuscript p. 1). -/
def bcdtCoeff {N : ℕ} {k : ℤ} (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) : ℂ :=
  (qExpansion 1 f).coeff n

/-- **"The L-function `L(E, s)` of `E` equals the L-function `L(f, s)`"** (condition (2), p. 3),
read as agreement of Mathlib's `L(E, s)` with `L(f, s) = ∑ c_n(f) n^{-s}` on a right half-plane. -/
def LFunctionsAgree (E : WeierstrassCurve ℚ) {N : ℕ} {k : ℤ}
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → E.LSeries s = LSeries (bcdtCoeff f) s

/-- **Breuil–Conrad–Diamond–Taylor, Theorem A, with the Introduction's condition (2)** (PRINT;
J. Amer. Math. Soc. 14 (2001) 843–939; read (AI) in the author manuscript, Theorem A p. 1, cusp
forms and `L(f, s)` p. 1, `T_p` and eigenforms p. 2, condition (2) p. 3; tex L1092
`\cite[Theorem A]{bcdt}`): for every elliptic curve `E/ℚ`, `L(E, s) = L(f, s)` for some
eigenform `f` of weight 2 and level `N`. Consequence form in one respect: the print's level is
the conductor `N(E)`, which has no definition in Mathlib or the tree; here the level is some
`N ≥ 1` (see `BCDTThmAPrintedAtLevel`). -/
def BCDTThmAPrinted : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic →
    ∃ (N : ℕ) (_ : NeZero N) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2),
      IsBCDTEigenform f ∧ LFunctionsAgree E f

/-- **Theorem A with condition (2) at a prescribed level**: as `BCDTThmAPrinted`, with the level
of `f` equal to `level E`. With `level` the conductor this is the print word for word. -/
def BCDTThmAPrintedAtLevel (level : WeierstrassCurve ℚ → ℕ) : Prop :=
  ∀ E : WeierstrassCurve ℚ, E.IsElliptic →
    ∃ (_ : NeZero (level E)) (f : CuspForm ((Gamma1 (level E)).map (mapGL ℝ)) 2),
      IsBCDTEigenform f ∧ LFunctionsAgree E f

/-- The prescribed-level statement gives `BCDTThmAPrinted` (forget the level). PROVED. -/
theorem bcdtThmAPrinted_of_atLevel (level : WeierstrassCurve ℚ → ℕ)
    (h : BCDTThmAPrintedAtLevel level) : BCDTThmAPrinted := fun E hE =>
  let ⟨i, f, hf⟩ := h E hE
  ⟨level E, i, f, hf⟩

/-! ### The local Euler factors of `E` -/

/-- The coefficients `c_k` of `1/(1 - aT + bT²)` satisfy `c₀ = 1`, `c₁ = a` and
`c_{k+2} = a c_{k+1} - b c_k`. -/
theorem coeff_invOfUnit_quadratic (a b : ℤ) :
    PowerSeries.coeff 0 (PowerSeries.invOfUnit
        ((1 - C a * X + C b * X ^ 2 : ℤ[X]) : PowerSeries ℤ) 1) = 1 ∧
    PowerSeries.coeff 1 (PowerSeries.invOfUnit
        ((1 - C a * X + C b * X ^ 2 : ℤ[X]) : PowerSeries ℤ) 1) = a ∧
    ∀ k : ℕ, PowerSeries.coeff (k + 2) (PowerSeries.invOfUnit
        ((1 - C a * X + C b * X ^ 2 : ℤ[X]) : PowerSeries ℤ) 1) =
      a * PowerSeries.coeff (k + 1) (PowerSeries.invOfUnit
        ((1 - C a * X + C b * X ^ 2 : ℤ[X]) : PowerSeries ℤ) 1) -
      b * PowerSeries.coeff k (PowerSeries.invOfUnit
        ((1 - C a * X + C b * X ^ 2 : ℤ[X]) : PowerSeries ℤ) 1) := by
  set Q := PowerSeries.invOfUnit ((1 - C a * X + C b * X ^ 2 : ℤ[X]) : PowerSeries ℤ) 1
  have hP : ((1 - C a * X + C b * X ^ 2 : ℤ[X]) : PowerSeries ℤ) =
      1 - PowerSeries.C a * PowerSeries.X ^ 1 + PowerSeries.C b * PowerSeries.X ^ 2 := by
    rw [Polynomial.coe_add, Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_mul,
      Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_C, Polynomial.coe_pow,
      Polynomial.coe_X, pow_one]
  have h0 : PowerSeries.constantCoeff ((1 - C a * X + C b * X ^ 2 : ℤ[X]) : PowerSeries ℤ) =
      ((1 : ℤˣ) : ℤ) := by
    rw [hP]; simp
  have hmul : (1 - PowerSeries.C a * PowerSeries.X ^ 1 + PowerSeries.C b * PowerSeries.X ^ 2) *
      Q = 1 := by
    rw [← hP]; exact PowerSeries.mul_invOfUnit _ _ h0
  have hcoeff : ∀ n : ℕ, PowerSeries.coeff n Q -
      a * (if 1 ≤ n then PowerSeries.coeff (n - 1) Q else 0) +
      b * (if 2 ≤ n then PowerSeries.coeff (n - 2) Q else 0) = if n = 0 then 1 else 0 := by
    intro n
    have := congrArg (PowerSeries.coeff n) hmul
    rw [PowerSeries.coeff_one] at this
    rw [← this, add_mul, sub_mul, one_mul, map_add, map_sub, mul_assoc, mul_assoc,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul',
      PowerSeries.coeff_X_pow_mul']
  have hQ0 : PowerSeries.coeff 0 Q = 1 := by simpa using hcoeff 0
  refine ⟨hQ0, ?_, fun k => ?_⟩
  · have := hcoeff 1
    simp only [le_refl, ite_true, Nat.sub_self, hQ0, show ¬ (2 ≤ 1) by norm_num, ite_false,
      mul_zero, add_zero, one_ne_zero, mul_one] at this
    linarith
  · have := hcoeff (k + 2)
    simp only [show 1 ≤ k + 2 by omega, show 2 ≤ k + 2 by omega, ite_true,
      show k + 2 ≠ 0 by omega, ite_false, show k + 2 - 1 = k + 1 by omega,
      show k + 2 - 2 = k by omega] at this
    linarith

/-- **The Euler factor of `E/ℚ` at a prime is `1 - aT + bT²` with `b = p` or `b = 0`** (good
reduction: `b = |𝔽_p| = p`; multiplicative or additive reduction: `b = 0`). -/
theorem exists_localPolynomial_eq (E : WeierstrassCurve ℚ)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    ∃ a b : ℤ, (E.baseChange (v.adicCompletion ℚ)).localPolynomial
        (v.adicCompletionIntegers ℚ) = 1 - C a * X + C b * X ^ 2 ∧
      (b = (natGenerator v : ℤ) ∨ b = 0) := by
  have hcard := ZInQ.Literature.natCard_residueField v
  unfold localPolynomial
  split_ifs
  · exact ⟨_, _, rfl, Or.inl (by rw [hcard])⟩
  · exact ⟨1, 0, by simp, Or.inr rfl⟩
  · exact ⟨-1, 0, by simp, Or.inr rfl⟩
  · exact ⟨0, 0, by simp, Or.inr rfl⟩

/-- **The Hecke relation of the coefficients of `L(E, s)` at a prime `p`**: with `b = p` or
`b = 0` as in `exists_localPolynomial_eq`, `a_p a_{pj} - a_{p²j} = b a_j` for every `j ≥ 1`. -/
theorem exists_LFunction_hecke (E : WeierstrassCurve ℚ) {p : ℕ} (hp : p.Prime) :
    ∃ b : ℤ, (b = p ∨ b = 0) ∧ ∀ j : ℕ, 0 < j →
      E.LFunction p * E.LFunction (p * j) - E.LFunction (p * (p * j)) = b * E.LFunction j := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨v, hv⟩ := ZInQ.Literature.exists_natGenerator_eq p
  obtain ⟨a, b, hP, hb⟩ := exists_localPolynomial_eq E v
  obtain ⟨h0, h1, hrec⟩ := coeff_invOfUnit_quadratic a b
  have hpow : ∀ k : ℕ, E.LFunction (p ^ k) = PowerSeries.coeff k (PowerSeries.invOfUnit
      ((1 - C a * X + C b * X ^ 2 : ℤ[X]) : PowerSeries ℤ) 1) := by
    intro k
    rw [← hv, ZInQ.Manuscript.RC.TwistDictionary.LFunction_prime_pow, hP]
  have hmul := ZInQ.Literature.isMultiplicative_LFunction E
  refine ⟨b, by rw [hv] at hb; exact hb, fun j hj => ?_⟩
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hj.ne' p hp.ne_one
  have hcop : ∀ i : ℕ, Nat.Coprime (p ^ i) m := fun i =>
    Nat.Coprime.pow_left i ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  have e1 : p * (p ^ e * m) = p ^ (e + 1) * m := by ring
  have e2 : p * (p * (p ^ e * m)) = p ^ (e + 2) * m := by ring
  have hp1 : E.LFunction p = a := by
    rw [← pow_one p, hpow 1, h1]
  rw [e2, e1, hmul.map_mul_of_coprime (hcop _), hmul.map_mul_of_coprime (hcop _),
    hmul.map_mul_of_coprime (hcop _), hp1, hpow, hpow, hpow, hrec e]
  ring

/-! ### The diamond operators fix `f` -/

section Hecke

variable {N : ℕ} [NeZero N]

theorem one_mem_strictPeriods (N : ℕ) [NeZero N] :
    (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods :=
  TauCeti.one_mem_strictPeriods_Gamma1_map N

/-- **Step 2: at a prime `p ∤ N`, `⟨p⟩ f = f`.** For an eigenvector `f` of `T_p` whose
coefficients are those of `L(E, s)`. -/
theorem diamondOpCuspNat_eq_self (E : WeierstrassCurve ℚ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2) (hf0 : f ≠ 0)
    (hc : ∀ n : ℕ, 0 < n → bcdtCoeff f n = (E.LFunction n : ℂ))
    {p : ℕ} [NeZero p] (hp : p.Prime) (hpN : ¬ p ∣ N) {lam : ℂ}
    (hlam : heckeTCuspNat 2 p f = lam • f) :
    diamondOpCuspNat 2 p f = f := by
  have hΓ := one_mem_strictPeriods N
  have hcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).2 hpN
  have hmul := ZInQ.Literature.isMultiplicative_LFunction E
  have hc' : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (E.LFunction n : ℂ) := hc
  have hc1 : (qExpansion 1 f).coeff 1 = 1 := by
    rw [hc' 1 one_pos, hmul.map_one]; simp
  rw [heckeTCuspNat_def] at hlam
  have hlamp := eq_qExpansion_coeff_of_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_eq_smul
    2 hp hlam hc1
  obtain ⟨b, hb, hrel⟩ := exists_LFunction_hecke E hp
  -- `p · c_j(⟨p⟩ f) = b · c_j(f)` for every `j`
  have hkey : ∀ j : ℕ, (p : ℂ) * (qExpansion 1 (diamondOpCuspNat 2 p f)).coeff j =
      (b : ℂ) * (qExpansion 1 f).coeff j := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [CuspFormClass.qExpansion_coeff_zero _ one_pos hΓ,
        CuspFormClass.qExpansion_coeff_zero _ one_pos hΓ]; simp
    have hr := qExpansion_coeff_heckeSlashGamma1CuspFormEnd_diagCosetGamma1_of_prime 2 hp f
      (p * j)
    rw [hlam, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos hΓ, map_smul, smul_eq_mul,
      ite_eq_left_of_eq_true _ _ (eq_true (dvd_mul_right p j)), Nat.mul_div_cancel_left j hp.pos,
      show (2 : ℤ) - 1 = 1 by norm_num, zpow_one] at hr
    have hpj : 0 < p * j := Nat.mul_pos hp.pos hj
    have hppj : 0 < p * (p * j) := Nat.mul_pos hp.pos hpj
    rw [hlamp] at hr
    rw [hc' p hp.pos, hc' _ hpj, hc' _ hppj] at hr
    rw [hc' j hj]
    have := congrArg (fun z : ℤ => (z : ℂ)) (hrel j hj)
    push_cast at this
    linear_combination this - hr
  have heq : (p : ℂ) • diamondOpCuspNat 2 p f = (b : ℂ) • f := by
    refine CuspForm.qExpansion_injective one_pos hΓ ?_
    refine PowerSeries.ext fun j => ?_
    simp only [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos hΓ, map_smul, smul_eq_mul]
    exact hkey j
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  rcases hb with rfl | rfl
  · simp only [Int.cast_natCast] at heq
    exact smul_right_injective _ hp0 heq
  · exfalso
    simp only [Int.cast_zero, zero_smul] at heq
    have h0 : diamondOpCuspNat 2 p f = 0 := (smul_eq_zero.mp heq).resolve_left hp0
    rw [diamondOpCuspNat_of_coprime 2 hcop] at h0
    apply hf0
    have := congrArg (diamondOpCusp 2 (ZMod.unitOfCoprime p hcop)⁻¹) h0
    rw [map_zero, ← LinearMap.comp_apply, ← diamondOpCusp_mul, inv_mul_cancel,
      diamondOpCusp_one, LinearMap.id_apply] at this
    exact this

/-- **Step 3: every diamond operator fixes `f`** (Dirichlet's theorem). -/
theorem diamondOpCusp_eq_self (E : WeierstrassCurve ℚ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2) (hf : IsBCDTEigenform f)
    (hc : ∀ n : ℕ, 0 < n → bcdtCoeff f n = (E.LFunction n : ℂ)) (d : (ZMod N)ˣ) :
    diamondOpCusp 2 d f = f := by
  obtain ⟨p, hpN, hp, hpd⟩ := Nat.forall_exists_prime_gt_and_eq_mod (q := N) d.isUnit N
  have hndvd : ¬ p ∣ N := fun h =>
    absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) h) (by omega)
  have hcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).2 hndvd
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨lam, hlam⟩ := hf.2 p hp hndvd
  have h := diamondOpCuspNat_eq_self E f hf.1 hc hp hndvd hlam
  rw [diamondOpCuspNat_of_coprime 2 hcop] at h
  have hu : ZMod.unitOfCoprime p hcop = d := Units.ext (by simpa using hpd)
  rwa [hu] at h

end Hecke

/-! ### Step 1: equal `L`-series have equal coefficients -/

theorem coeff_eq_of_LFunctionsAgree (E : WeierstrassCurve ℚ) (hE : E.IsElliptic) {N : ℕ}
    [NeZero N] (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2) (hL : LFunctionsAgree E f) :
    ∀ n : ℕ, 0 < n → bcdtCoeff f n = (E.LFunction n : ℂ) := by
  obtain ⟨σ, hσ⟩ := hL
  have hconv := ZInQ.Contrib.CloudB3RC53.Hasse.hasseConvergence_proof
    (fun F _ _ W _ => ZInQ.Contrib.CloudB3RC53.WeilIsogeny.hasseBoundProved_proof F W)
  have hEs : LSeriesSummable (fun n => ((E.LFunction n : ℤ) : ℂ)) 2 :=
    hconv E hE 2 (by norm_num)
  have hEa : abscissaOfAbsConv (fun n => ((E.LFunction n : ℤ) : ℂ)) < ⊤ :=
    (hEs.abscissaOfAbsConv_le).trans_lt (EReal.coe_lt_top _)
  have hfa : abscissaOfAbsConv (bcdtCoeff f) < ⊤ := by
    have := CuspForm.abscissaOfAbsConv_qExpansion_coeff_le (Γ := (Gamma1 N).map (mapGL ℝ))
      (k := 2) f
    rw [show ((Gamma1 N).map (mapGL ℝ)).strictWidthInfty = 1 from
      strictWidthInfty_Gamma1 N] at this
    exact this.trans_lt (EReal.add_lt_top (EReal.coe_ne_top _) (by decide))
  intro n hn
  refine (LSeries.eq_of_LSeries_eventually_eq hEa hfa ?_ hn.ne').symm
  refine Filter.eventually_atTop.2 ⟨σ + 1, fun x hx => ?_⟩
  have := hσ x (by rw [Complex.ofReal_re]; linarith)
  exact this

/-! ### The headline hypothesis from the print -/

/-- **Modularity in the headline's sense from one instance of condition (2)** (PROVED): an
eigenform `f` of weight 2 on `Γ₁(N)` with `L(f, s) = L(E, s)` has trivial nebentypus, and as a
cusp form on `Γ₀(N)` its coefficients are those of `L(E, s)`. -/
theorem isModular_of_eigenform (E : WeierstrassCurve ℚ) (hE : E.IsElliptic) {N : ℕ} [NeZero N]
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) 2) (hf : IsBCDTEigenform f)
    (hL : LFunctionsAgree E f) : ZInQ.Manuscript.PoleS12.IsModular E := by
  have hc := coeff_eq_of_LFunctionsAgree E hE f hL
  have hmem : f ∈ cuspFormCharSpace (N := N) 2 (1 : (ZMod N)ˣ →* ℂˣ) :=
    (TauCeti.mem_cuspFormCharSpace_one_iff_diamondOpCusp f).2
      (diamondOpCusp_eq_self E f hf hc)
  set g := TauCeti.cuspFormCharSpaceOneEquiv N 2 ⟨f, hmem⟩
  have hg : ⇑g = ⇑f := TauCeti.coe_cuspFormCharSpaceOneEquiv_apply _
  refine ⟨N, Nat.pos_of_ne_zero (NeZero.ne N), g, fun n hn => ?_⟩
  rw [show qExpansion 1 g = qExpansion 1 f from congrArg (qExpansion 1) hg]
  exact hc n hn

/-- **`PoleS12.BCDTThmA` from Breuil–Conrad–Diamond–Taylor's Theorem A as printed** (PROVED). -/
theorem bcdtThmA_of_printed (h : BCDTThmAPrinted) : ZInQ.Manuscript.PoleS12.BCDTThmA := by
  intro E hE
  obtain ⟨N, _, f, hf, hL⟩ := h E hE
  exact isModular_of_eigenform E hE f hf hL

/-- **`PoleS12.BCDTThmA` from Theorem A at a prescribed level** (PROVED). -/
theorem bcdtThmA_of_printedAtLevel (level : WeierstrassCurve ℚ → ℕ)
    (h : BCDTThmAPrintedAtLevel level) : ZInQ.Manuscript.PoleS12.BCDTThmA :=
  bcdtThmA_of_printed (bcdtThmAPrinted_of_atLevel level h)

end ZInQ.Contrib.CloudB3E2.BCDT
