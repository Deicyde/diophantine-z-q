import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Newform

/-!
# Lane RC8: Hoffstein–Luo (nonvanishing twists with at most four prime factors) and the twisted
functional equation

**Uses in the manuscript (11/5 text).** tex L1984–1991 (`ex:sec7-nonvanishing`): "Choose a signed
prime `q₀` in the prescribed unit classes by Dirichlet's theorem, avoiding `S ∪ B`. Apply
Hoffstein–Luo [hl] in the even case, or Bump–Friedberg–Hoffstein [bfh] in the odd case, to the
actual curve `E^{(q₀)}`. Require their positive discriminant `d` to split at `S ∪ B ∪ {|q₀|}` and at
the conductor primes. Then `q₀d` has the prescribed original classes. Hoffstein–Luo gives at most
four prime factors of `d`, so at most five in total." App G L9995–9999: "The theorem of
Hoffstein–Luo [hl, p. 436] supplies fundamental discriminants with nonzero central value and at
most four prime factors. Its finite splitting set is arbitrary." App G L10016–10027
(`ex:app-five-prime`): apply the theorem to `A^{q₀}` with splitting set
`S' = S ∪ B ∪ {|q₀|} ∪ {p : p ∣ N_{A^{q₀}}}`; "The functional equation forces `d > 0`, since
`A^{q₀}` has even root number and every conductor prime splits. Splitting at two gives
`d ≡ 1 (mod 8)`." Also App G L10049–10051 (the rough companion, `E^{hk₀}`).

**The print** (J. Hoffstein and W. Luo, *Nonvanishing of L-series and the combinatorial sieve*,
with an appendix by D. E. Rohrlich, Math. Res. Lett. 4 (1997), 435–444; read in the publisher's
PDF). §1, p. 435: "Let `f(z) = ∑ aₙ e(nz)` be a normalized holomorphic newform of weight `k ≥ 2`,
level `N` with trivial nebentype as in [8], and let `L(s, f)` be the associated Hecke L-function.
For any fundamental discriminant `d`, `(d, N) = 1`, we have the Kronecker symbol `χ_d(·) = (d/·)`,
and the corresponding twisted L-function `L(s, f, χ_d)`. It was proved by Hecke [5], by means of
Mellin inversion, that the L-function `L(s, f, χ_d)` is an entire function of `s` and satisfies the
functional equation
`(|d|√N/2π)^s Γ(s) L(s, f, χ_d) = w χ_d(-N) (|d|√N/2π)^{k-s} Γ(k - s) L(k - s, f, χ_d)`   (1)
where `w = ±1` is the root number."
**Theorem** (unnumbered, pp. 435–436). "There exist infinitely many odd fundamental discriminants
`d` such that `L(k/2, f, χ_d) ≠ 0` (2) and the number of prime factors of `d` is no greater than 4.
Moreover if `S` is any finite set of rational primes then there exist infinitely many odd
fundamental discriminants `d` with the above properties and such that `χ_d(p) = 1` for all
`p ∈ S`."

The Lean statements are over Tau Ceti's genuine newforms (`Newform.lean`); `(d, N) = 1` is part of
the print's setting (the theorem's `d` lie in
`Δ_w = {d : ±d > 0, μ(d) ≠ 0, d ≡ ν² (mod 4M) for some ν coprime to 4M}`, §2, `N ∣ M`; the `ν`
clause gives `(d, 4M) = 1`), so it is included in the conclusion; it also follows by putting the
primes of `N` into `S`. The bound four on `ω(d)` is §3's `r = 4`, whose details are "suppressed"
(p. 441); the theorem as printed is the leaf.

**Use check.** Hoffstein–Luo is applied to the newform of `A^{q₀}` (weight 2, trivial nebentypus,
`k ≥ 2` ✓); the splitting set is arbitrary ✓; the bound four on `ω(d)` is absolute ✓ (it does not
depend on `f` or `S`); `d` is odd ✓. The theorem does not say `d > 0`: that is forced by (1), as
App G L10025 says, and is `pos_of_twisted_functional_equation` below (PROVED from (1)). The
identification `L(s, f, χ_d) = L(A^{(d)}, s)` for the curve is `TwistDictionary` (GLUE,
`Newform.lean`); the curve forms over the shared vocabulary are `HoffsteinLuoCurve` and
`TwistedRootNumberCurve`, and `pos_of_twistedRootNumber` is the step `d > 0`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.PrintsAnalytic

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 HeckeRing.GL2 Complex

/-- **Hoffstein–Luo, Theorem** (PRINT; Math. Res. Lett. 4 (1997) 435–444, §1, pp. 435–436).
For a newform `f` of weight `k ≥ 2`, level `N`, trivial nebentypus, and any finite set `S` of
primes, there are infinitely many odd fundamental discriminants `d`, prime to `N`, with at most four
prime factors, `χ_d(p) = 1` for every `p ∈ S`, and `L(k/2, f, χ_d) ≠ 0`; here `L(s, f, χ_d)` is the
entire continuation (Hecke) of `∑ χ_d(n) aₙ n^{-s}` from `Re s > k/2 + 1`. -/
def HoffsteinLuoTheorem : Prop :=
  ∀ (N : ℕ) [NeZero N] (k : ℤ) (f : Newform N k), f.χ = 1 → 2 ≤ k →
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
      {d : ℤ | IsFundamentalDiscriminant d ∧ Odd d ∧ IsCoprime d (N : ℤ) ∧ omega d ≤ 4 ∧
        (∀ p ∈ S, kronecker d p = 1) ∧
        ∃ F : ℂ → ℂ, IsEntireContinuation (twistCoeff (nfCoeff f) d) ((k : ℝ) / 2 + 1) F ∧
          F ((k : ℂ) / 2) ≠ 0}.Infinite

/-- **The twisted functional equation** (PROVED by lane RC33 as
`twistedFunctionalEquation_proved`, `TwistedFE.lean`, in every weight; stated here as quoted in
Hoffstein–Luo p. 435, display (1), "proved by Hecke [5]", and in Bump–Friedberg–Hoffstein,
Invent. Math. 102 (1990), p. 543:
"`Λ(s, f, χ_D) = (D²M)^{s/2}(2π)^{-s}Γ(s)L(s, f, χ_D)` ... provided `gcd(M, D) = 1`, satisfies the
functional equation `Λ(s, f, χ_D) = εχ_D(-M)Λ(k - s, f, χ_D)`"). For a newform `f` of trivial
nebentypus, weight `k`, level `N`, sign `ε = newformSign f` (`Λ(s, f) = εΛ(k - s, f)`), and a
fundamental discriminant `D` prime to `N`, the twisted series has an entire continuation `F`
with `Λ_{D²N}(k - s) = ε χ_D(-N) Λ_{D²N}(s)` on `0 < Re s < k`, where
`χ_D(-N) = sgn(D) χ_D(N)` and `Λ_{D²N}(s) = (D²N)^{s/2}(2π)^{-s}Γ(s)F(s) = (|D|√N/2π)^s Γ(s) F(s)`. -/
def TwistedFunctionalEquation : Prop :=
  ∀ (N : ℕ) [NeZero N] (k : ℤ) (f : Newform N k) (hχ : f.χ = 1), 0 < k →
    ∀ D : ℤ, IsFundamentalDiscriminant D → IsCoprime D (N : ℤ) →
      ∃ F : ℂ → ℂ, IsEntireContinuation (twistCoeff (nfCoeff f) D) ((k : ℝ) / 2 + 1) F ∧
        ∀ s : ℂ, 0 < s.re → s.re < k →
          completedL (D.natAbs ^ 2 * N) F (k - s) =
            newformSign f hχ * ((kroneckerNegOne D * kronecker D N : ℤ) : ℂ) *
              completedL (D.natAbs ^ 2 * N) F s

/-- **Hoffstein–Luo for an elliptic curve** (PRINT, composite: the form used at tex L1985–1991 and
App G L9995–10027, over the shared vocabulary `qtwist`, `AnalyticRank`). For every elliptic curve
`A/ℚ` and every finite set `S` of primes there are infinitely many odd fundamental discriminants
`d` with `ω(d) ≤ 4`, `χ_d(p) = 1` for every `p ∈ S`, and `ord_{s=1} L(A^{(d)}, s) = 0`, i.e.
`L(A^{(d)}, 1) ≠ 0`. This is `HoffsteinLuoTheorem` applied to the newform of `A` (modularity,
`ModularNewform`), with `L(s, f, χ_d) = L(A^{(d)}, s)` for `d` prime to the level (`TwistDictionary`,
GLUE; the print's `d` are prime to the level) and the convention `Re s > 3/2`
(`HasseConvergence`, GLUE); `Bridges.lean` proves `hoffsteinLuoCurve_of` from these. No hypothesis
on `S` is needed: the print's `d` are always prime to the level. -/
def HoffsteinLuoCurve : Prop :=
  ∀ A : WeierstrassCurve ℚ, A.IsElliptic → ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) →
    {d : ℤ | IsFundamentalDiscriminant d ∧ Odd d ∧ omega d ≤ 4 ∧
      (∀ p ∈ S, kronecker d p = 1) ∧ AnalyticRank (qtwist A d) 0}.Infinite

/-- **The twisted functional equation for an elliptic curve** (PRINT, composite: display (1) of
Hoffstein–Luo p. 435 and BFH p. 543 for the newform of `A`, with `TwistDictionary`). If `L(A, s)`
has the functional equation of level `N` and sign `w`, and `D` is a fundamental discriminant prime
to `N`, then `L(A^{(D)}, s)` has the functional equation of level `D²N` and sign
`w χ_D(-N) = w · sgn(D) · χ_D(N)`. Used at App G L10025 ("The functional equation forces
`d > 0`"), through `pos_of_twistedRootNumber`. -/
def TwistedRootNumberCurve : Prop :=
  ∀ A : WeierstrassCurve ℚ, A.IsElliptic → ∀ (N : ℕ) (w : ℤ), RootNumberAt A N w →
    ∀ D : ℤ, IsFundamentalDiscriminant D → IsCoprime D (N : ℤ) →
      RootNumberAt (qtwist A D) (D.natAbs ^ 2 * N) (w * (kroneckerNegOne D * kronecker D N))

/-! ### `d > 0` from the twisted functional equation (App G L10025) -/

/-- The Jacobi symbol `J(D | m)` is `1` when `J(D | p) = 1` for every prime `p ∣ m` (PROVED). -/
theorem jacobiSym_eq_one_of_forall_prime_dvd {D : ℤ} :
    ∀ m : ℕ, (∀ p : ℕ, p.Prime → p ∣ m → jacobiSym D p = 1) → jacobiSym D m = 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro h
    rcases Nat.lt_or_ge m 2 with hm | hm
    · interval_cases m
      · exact jacobiSym.zero_right D
      · exact jacobiSym.one_right D
    · have hp := Nat.minFac_prime (show m ≠ 1 by omega)
      obtain ⟨c, hc⟩ := Nat.minFac_dvd m
      have hc0 : c ≠ 0 := by rintro rfl; omega
      have hcm : c < m := by
        rw [hc]
        have := hp.two_le
        nlinarith [Nat.pos_of_ne_zero hc0]
      have : NeZero m.minFac := ⟨hp.ne_zero⟩
      have : NeZero c := ⟨hc0⟩
      rw [hc, jacobiSym.mul_right, h _ hp (Nat.minFac_dvd m),
        ih c hcm fun p hp' hpc => h p hp' (hc ▸ Dvd.dvd.mul_left hpc _), one_mul]

/-- `χ_D(N) = 1` when every prime factor of `N` splits in `ℚ(√D)` (PROVED). -/
theorem kronecker_eq_one_of_forall_prime_dvd {D : ℤ} {N : ℕ} (hN : N ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ N → kronecker D p = 1) : kronecker D N = 1 := by
  unfold kronecker
  have h2 : kroneckerTwo D ^ N.factorization 2 = 1 := by
    by_cases h2N : 2 ∣ N
    · have := h 2 Nat.prime_two h2N
      simp only [kronecker, Nat.Prime.factorization_self Nat.prime_two, pow_one,
        Nat.div_self (show 0 < 2 by norm_num), jacobiSym.one_right, mul_one] at this
      rw [this, one_pow]
    · rw [Nat.factorization_eq_zero_of_not_dvd h2N, pow_zero]
  rw [h2, one_mul]
  apply jacobiSym_eq_one_of_forall_prime_dvd
  intro p hp hpd
  have hpN : p ∣ N := (hpd.trans (Nat.div_dvd_of_dvd (Nat.ordProj_dvd N 2)))
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact Nat.not_dvd_ordCompl Nat.prime_two hN hpd
  have := h p hp hpN
  simpa [kronecker, Nat.factorization_eq_zero_of_not_dvd (fun h2 => hp2
    ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h2).symm)] using this

/-- **`d > 0` from the twisted functional equation** (PROVED; the step "The functional equation
forces `d > 0`, since `A^{q₀}` has even root number and every conductor prime splits", App G
L10025). If the twisted completed L-function of level `D²N` satisfies the functional equation of
sign `ε χ_D(-N)` on the strip, `ε = 1`, every prime factor of `N` splits in `ℚ(√D)`, and the central
value `F(k/2)` is nonzero, then `D > 0`. -/
theorem pos_of_twisted_functional_equation {N : ℕ} (hN : 0 < N) {k : ℕ} (hk : 0 < k) {D : ℤ}
    (hD : D ≠ 0) {F : ℂ → ℂ} {ε : ℂ} (hε : ε = 1)
    (hFE : ∀ s : ℂ, 0 < s.re → s.re < k →
      completedL (D.natAbs ^ 2 * N) F (k - s) =
        ε * ((kroneckerNegOne D * kronecker D N : ℤ) : ℂ) * completedL (D.natAbs ^ 2 * N) F s)
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ N → kronecker D p = 1) (hF : F ((k : ℂ) / 2) ≠ 0) :
    0 < D := by
  have hN' : 0 < D.natAbs ^ 2 * N := Nat.mul_pos (pow_pos (Int.natAbs_pos.mpr hD) 2) hN
  have h1 := sign_eq_one_of_central_ne_zero hN' hk hFE hF
  rw [hε, one_mul, kronecker_eq_one_of_forall_prime_dvd hN.ne' hsplit, mul_one,
    kroneckerNegOne] at h1
  have h1' : Int.sign D = 1 := by exact_mod_cast h1
  exact Int.sign_eq_one_iff_pos.mp h1'

/-- **`d > 0` for the twisted curve** (PROVED; App G L10025, "The functional equation forces
`d > 0`, since `A^{q₀}` has even root number and every conductor prime splits"). If `A^{(D)}` has
the functional equation of level `D²N` and sign `1 · χ_D(-N)` (the output of
`TwistedRootNumberCurve` when `A` has root number `+1`), every prime factor of `N` splits in
`ℚ(√D)`, and `L(A^{(D)}, 1) ≠ 0`, then `D > 0`. -/
theorem pos_of_twistedRootNumber {A : WeierstrassCurve ℚ} {N : ℕ} (hN : 0 < N) {D : ℤ}
    (hD : D ≠ 0)
    (hroot : RootNumberAt (qtwist A D) (D.natAbs ^ 2 * N) (1 * (kroneckerNegOne D * kronecker D N)))
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ N → kronecker D p = 1)
    (h0 : AnalyticRank (qtwist A D) 0) : 0 < D := by
  obtain ⟨-, F', hF', hFE⟩ := hroot
  obtain ⟨F, hF, hF1⟩ := analyticRank_zero_iff.mp h0
  have hEq : F' = F := isLContinuation_eq hF' hF
  subst hEq
  refine pos_of_twisted_functional_equation (F := F') hN (k := 2) (by norm_num) hD (ε := 1) rfl ?_
    hsplit ?_
  · intro s hs1 hs2
    have h := hFE s hs1 (by exact_mod_cast hs2)
    push_cast at h ⊢
    simpa using h
  · simpa using hF1

end ZInQ.Manuscript.RC.PrintsAnalytic
