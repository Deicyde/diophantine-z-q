import ZInQKernel.Contrib.OneProof.RC.Nonvanishing.Basic
import ZInQKernel.Contrib.OneProof.PoleS12.Leaves

/-!
# Lane RC13 (nonvanishing), part 3: the printed leaves

The printed theorems the nonvanishing proposition rests on (tex 1985–1997, 9996–10026), each
stated as a `Prop` over the genuine definitions of part 1 (Mathlib's `L`-series of the twist, its
entire continuation and functional equation). They are hypotheses of the deductions in parts 4
and 5, never proved here. All three prints were read for this lane (locators below).

* `HoffsteinLuoBound r` / `HoffsteinLuo` (PRINT): Hoffstein–Luo, *Nonvanishing of `L`-series and
  the combinatorial sieve*, Math. Res. Lett. 4 (1997), no. 3, 435–444, **Theorem, pp. 435–436**.
* `BFHSimpleZero`, `BFHNonvanishing` (PRINT): Bump–Friedberg–Hoffstein, *Nonvanishing theorems
  for `L`-functions of modular forms and their derivatives*, Invent. Math. 102 (1990), 543–618,
  **Theorem, pp. 543–544, clauses (i) and (ii)**.
* `BFHTwistSign` (PRINT): the same paper, **p. 543, the paragraph before the Theorem** (the sign
  of the functional equation of `L(s, f, χ_D)` when every prime of the level splits in `ℚ(√D)`);
  the same functional equation is (1) on p. 435 of Hoffstein–Luo.
* `LocalRootNumbers` (interface, PRINT + GLUE): local root numbers `W_p(E)`, `W_∞(E)` are not in
  Mathlib; the structure records the properties the root-number check (tex 1994–2001) uses, one
  of which is Desjardins, *Root number of twists of an elliptic curve*, J. Théor. Nombres
  Bordeaux 32 (2020), no. 1, 73–101, **Proposition 3.3 (case (2), type `I₀`), p. 84**.

**From newforms to curves (GLUE, folded into each leaf).** The prints are about a newform `f` of
weight `2k` (here `2`), level `N`, trivial character, and the twisted series
`L(s, f, χ_D) = Σ χ_D(n) a_n(f) n^{-s}` for `gcd(D, N) = 1`. Each leaf is stated for a modular
elliptic curve `A/ℚ` (`PoleS12.IsModular`), its newform `f` (modularity, BCDT) and
`L(A^{(D)}, s) = L(s, f, χ_D)` for `gcd(D, N) = 1` (the newform of `A^{(D)}` is `f ⊗ χ_D`). The
level `N` is replaced by the set of primes at which the model of `A` is not good, which contains
the primes of `N`: requiring every such prime to lie in (or split in) a set is stronger than the
print's requirement on the primes of `N`, so each leaf is implied by its print.
-/

namespace ZInQ.Manuscript.RC.Nonvanishing

open ZInQ.Manuscript ZInQ.Manuscript.PoleS12 ZInQ.Contrib.CloudB3RC53

/-- **Hoffstein–Luo, with the bound `r` on the number of prime factors** (PRINT for `r = 4`; Math.
Res. Lett. 4 (1997), 435–444, Theorem, pp. 435–436): for a modular elliptic curve `A/ℚ` and any
finite set `S` of primes (here containing every prime at which the model is not good), there are
infinitely many odd fundamental discriminants `d` with at most `r` prime factors, `χ_d(p) = 1`
for every `p ∈ S`, and `L(A^{(d)}, 1) ≠ 0`.

The print: "There exist infinitely many odd fundamental discriminants `d` such that
`L(k/2, f, χ_d) ≠ 0` and the number of prime factors of `d` is no greater than `4`. Moreover if
`S` is any finite set of rational primes then there exist infinitely many odd fundamental
discriminants `d` with the above properties and such that `χ_d(p) = 1` for all `p ∈ S`."
(`f` a normalized holomorphic newform of weight `k ≥ 2`, level `N`, trivial nebentype; `d` with
`(d, N) = 1`, p. 435.) The print imposes no sign on `d`; the sign is forced by the functional
equation (tex 10025–10026, `fivePrime`). The bound is a parameter so that the deduction is
visibly absolute: §2 of the print proves the statement for some absolute `r`, and §3 obtains
`r = 4` by a metaplectic estimate whose details the authors say they suppress (p. 441). -/
def HoffsteinLuoBound (r : ℕ) : Prop :=
  ∀ A : WeierstrassCurve ℚ, A.IsElliptic → IsModular A →
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → ¬ GoodAt A p → p ∈ S) →
      {d : ℤ | IsFundamentalDiscriminant d ∧ Odd d ∧ omega d ≤ r ∧ (∀ p ∈ S, SplitsIn d p) ∧
        CentralNonzero (qtwist A d)}.Infinite

/-- **Hoffstein–Luo** (PRINT; Math. Res. Lett. 4 (1997), Theorem, pp. 435–436), with the printed
bound `4`, as the manuscript cites it (tex 1990–1991, `\cite[p.~436]{hl}` at 9996). -/
def HoffsteinLuo : Prop := HoffsteinLuoBound 4

/-- **Bump–Friedberg–Hoffstein, clause (i)** (PRINT; Invent. Math. 102 (1990), 543–618, Theorem,
pp. 543–544): for a modular elliptic curve `A/ℚ` with root number `ε` and a finite set `S` of
primes containing the primes of the level (here: every prime at which the model is not good),
there is a fundamental discriminant `D` with `wD < 0` (`w` the root number), every prime of `S` split in `ℚ(√D)`, and
`L(s, A^{(D)})` with a simple zero at `s = 1`.

The print: "Let `f` be cuspidal newform of even weight `k` with trivial character for the group
`Γ₀(M)`, and let `S` be a finite set of primes including all those dividing `M`. Let `ε` denote the
sign in the functional equation of `f`. (i) There exists a quadratic field `ℚ(√D)` with `D` a
fundamental discriminant, and `εD < 0`, such that every prime in `S` splits in `ℚ(√D)`, and
`L(s, f, χ_D)` has a simple zero at `s = k/2`." This is the "simple-zero clause" of tex 1992. -/
def BFHSimpleZero : Prop :=
  ∀ A : WeierstrassCurve ℚ, A.IsElliptic → IsModular A → ∀ w : ℤ, RootNumber A w →
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → ¬ GoodAt A p → p ∈ S) →
      ∃ D : ℤ, IsFundamentalDiscriminant D ∧ w * D < 0 ∧ (∀ p ∈ S, SplitsIn D p) ∧
        AnalyticRank (qtwist A D) 1

/-- **Bump–Friedberg–Hoffstein, clause (ii)** (PRINT; Invent. Math. 102 (1990), Theorem,
pp. 543–544): in the setting of `BFHSimpleZero`, there is a fundamental discriminant `D` with
`wD > 0`, every prime of `S` split in `ℚ(√D)`, and `L(1, A^{(D)}) ≠ 0`. The print: "(ii) There
exists a quadratic field `ℚ(√D)` with `D` a fundamental discriminant, and `εD > 0`, such that every
prime in `S` splits in `ℚ(√D)`, and `L(k/2, f, χ_D) ≠ 0`." (Used for the genus partner `h_*`, App F
8251–8254; not used by the nonvanishing proposition itself.) -/
def BFHNonvanishing : Prop :=
  ∀ A : WeierstrassCurve ℚ, A.IsElliptic → IsModular A → ∀ w : ℤ, RootNumber A w →
    ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → ¬ GoodAt A p → p ∈ S) →
      ∃ D : ℤ, IsFundamentalDiscriminant D ∧ 0 < w * D ∧ (∀ p ∈ S, SplitsIn D p) ∧
        CentralNonzero (qtwist A D)

/-- **The sign of the twisted functional equation** (PRINT; Bump–Friedberg–Hoffstein, Invent.
Math. 102 (1990), p. 543; also Hoffstein–Luo, MRL 4, p. 435, (1)): if `D` is a fundamental
discriminant and every prime of the level splits in `ℚ(√D)` (here: every prime at which the model
is not good), then the twist has root number `sgn(D) · w`.

The print: "`Λ(s, f, χ_D) = (D²M)^{s/2}(2π)^{-s}Γ(s)L(s, f, χ_D)` … provided `gcd(M, D) = 1`,
satisfies the functional equation `Λ(s, f, χ_D) = εχ_D(−M)Λ(k − s, f, χ_D)`. Now suppose that every
prime dividing `M` splits in `ℚ(√D)`. … this implies that `χ_D(M) = 1`. Therefore the sign in the
functional equation for `L(s, f, χ_D)` is the same as the sign in the functional equation for
`L(s, f)` if `D > 0`, and opposite if `D < 0`." Used at tex 10025–10026 ("the functional equation
forces `d > 0`") and 10046 (`w(E^{hk₀}) = w(E^h)χ_{k₀}(−N_{E^h}) = +1`). -/
def BFHTwistSign : Prop :=
  ∀ A : WeierstrassCurve ℚ, A.IsElliptic → IsModular A → ∀ w : ℤ, RootNumber A w →
    ∀ D : ℤ, IsFundamentalDiscriminant D → (∀ p : ℕ, p.Prime → ¬ GoodAt A p → SplitsIn D p) →
      RootNumber (qtwist A D) (Int.sign D * w)

/-- **Local root numbers** (an interface: Mathlib has no Weil–Deligne representations or epsilon
factors). `w p E` is the local root number `W_p(E) ∈ {±1}` at a prime `p` and `wInf E` is
`W_∞(E)`, as defined by Rohrlich and recalled by Desjardins (JTNB 32 (2020), p. 73). The fields
are the properties the root-number check of tex 1994–2001 uses:

* `wInf_eq` (GLUE; Desjardins p. 73: "we always have `W_∞(E) = −1`");
* `w_good` (GLUE; Rohrlich; Desjardins p. 83, type `I₀`): `W_p(E) = 1` at a prime of good
  reduction;
* `global` (GLUE; Desjardins pp. 73–74: `W(E) = ∏_{p ≤ ∞} W_p(E)` "is equal to the sign of the
  functional equation of `L` by the Modularity Theorem over `ℚ`"): for a modular curve and a finite
  set `T` of primes containing every prime at which the model is not good, `E` has root number
  `ε` (in the sense of the blueprint's `RootNumber`) exactly when `ε = W_∞(E) ∏_{p ∈ T} W_p(E)`;
* `w_iso` (GLUE; local root numbers depend only on the curve over `ℚ_p`): if `u'/u` is a square
  in `ℚ_p` then `A^{(u)} ≅ A^{(u')}` over `ℚ_p`, so `W_p(A^{(u)}) = W_p(A^{(u')})` — "at the primes
  in `S` equal squareclasses give isomorphic local curves" (tex 1995–1996);
* `desjardins` (PRINT; **Desjardins, Proposition 3.3, p. 84, case (2), type `I₀`**): for a prime
  `p ≠ 2, 3` of good reduction and a squarefree `t` divisible by `p`, `W_p(E) = D_p W_p(E_t)` with
  `D_p = (−1/p)`. (The print is for `y² = x³ + ax + b` and `E_t : y² = x³ + at²x + bt³`; a curve
  good at `p ≥ 5` has such a model over `ℤ_(p)`, and `W_p` is an isomorphism invariant.) -/
structure LocalRootNumbers where
  /-- the local root number `W_p(E)` at a prime `p` -/
  w : ℕ → WeierstrassCurve ℚ → ℤ
  /-- the archimedean root number `W_∞(E)` -/
  wInf : WeierstrassCurve ℚ → ℤ
  wInf_eq : ∀ E : WeierstrassCurve ℚ, E.IsElliptic → wInf E = -1
  w_good : ∀ (E : WeierstrassCurve ℚ) (p : ℕ), E.IsElliptic → p.Prime → GoodAt E p → w p E = 1
  global : ∀ E : WeierstrassCurve ℚ, E.IsElliptic → IsModular E →
    ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime) → (∀ p : ℕ, p.Prime → ¬ GoodAt E p → p ∈ T) →
      ∀ ε : ℤ, RootNumber E ε ↔ ε = wInf E * ∏ p ∈ T, w p E
  w_iso : ∀ (E : WeierstrassCurve ℚ) (p : ℕ), E.IsElliptic → p.Prime →
    ∀ u u' : ℤ, u ≠ 0 → u' ≠ 0 → IsSquareAt p ((u' : ℚ) / u) →
      w p (qtwist E u) = w p (qtwist E u')
  desjardins : ∀ (E : WeierstrassCurve ℚ) (p : ℕ) [Fact p.Prime], E.IsElliptic → 5 ≤ p →
    GoodAt E p → ∀ t : ℤ, Squarefree t → (p : ℤ) ∣ t →
      w p E = legendreSym p (-1) * w p (qtwist E t)

end ZInQ.Manuscript.RC.Nonvanishing
