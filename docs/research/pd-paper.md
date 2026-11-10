# Proposition D in full: the good slope primes have positive density

Status: research note, 2026-11-09. Each claim carries a mark:
**VERIFIED** (checked against the manuscript, the Lean source or Mathlib, or by a computation, which is
cited), **STANDARD** (a published theorem whose statement was checked to apply; reference given),
**SPECULATIVE** (an idea, unproved) or **UNCHECKED** (a source that could not be read; the statement is
quoted from memory and must be checked before use). Manuscript line numbers refer to `diophantine_zq.tex`
(11/5 version). Mathlib means the pinned revision `56a005855ea1` (Lean 4.35.0). PrimeNumberTheoremAnd
means the tag `v4.34.0` (commit `c39a7511`). Scripts and their outputs are in `scratch/pd-paper/`.

Notation. `G = {p : ZInQ.GoodSlopePrime p}`. For an odd prime `p`, `χ = χ_p` is the quadratic character
of `𝔽_p` (Mathlib `quadraticChar (ZMod p)`), and for `a ∈ 𝔽_p`

  `φ_p(a) = Σ_{x∈𝔽_p} χ(x³ + ax) ∈ ℤ`.

`π(N)` is the number of primes `≤ N`, `θ_S(N) = Σ_{p∈S, p≤N} log p` and, for `x > 1`,
`Φ_S(x) = Σ_{p∈S} (log p)/p^x`. Letters `ℓ` and `q` always denote primes.

## Summary

1. **Target.** `G` has positive relative upper density:
   `∃ c > 0, ∃ᶠ N in atTop, c·π(N) ≤ #(G ∩ [0, N])` (`GTSearch.PrimesRelUpperDensityPos`, the hypothesis
   of Green–Tao 2008, Theorem 1.2). It is deduced from a positive lower Dirichlet density:
   `liminf_{x→1⁺} (x − 1)Φ_G(x) > 0` (Theorem D, §5). The implication from Dirichlet density to upper
   density is Proposition 5.3. It needs only Abel summation and Chebyshev's bound `π(N) ≪ N/log N`.
2. **The arithmetic description needs no CM theory** (§1). For `p ≡ 1 (mod 8)` with `(p/7) = −1`, put
   `c_p = φ_p(1)/2`. Then `p = c_p² + e_p²` with `c_p` odd, the two point counts in `GoodSlopePrime`
   are `p + 1 ∓ 2c_p`, and their gcd is exactly `4·gcd(c_p, p + 1)`. The proof uses only elementary
   character sums: the substitution `x ↦ kx`, one involution `x ↦ −D²/x`, and Jacobsthal's identity
   `φ_p(1)² + φ_p(r)² = 4p`. The endomorphism ring, Tate modules, the Hasse bound and Jacobi sums are
   all avoided. An odd prime dividing `gcd(c_p, p + 1)` is `≡ 1 (mod 4)`.
   VERIFIED (by hand, and by computation for every prime below `2·10⁴`, resp. `3·10⁴`).
3. **The "Frobenius" conditions are congruences** (§2). The only Chebotarev-type conditions are
   `p ≡ 1 (mod 8)` and `p mod 7 ∈ {3, 5, 6}`. They are conditions in the abelian field `ℚ(ζ₈, √7)`, so
   Dirichlet's theorem for residue classes suffices. Mathlib has it in exactly the needed form,
   `ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound`. Neither Chebotarev, nor Hecke for
   `ℚ(i)`, nor Artin induction is needed (§3). The chosen subset is
   `G*_L = C_L ∖ T_L`, where `C_L` is the set of primes with `p ≡ 1 (mod 8)`, `p mod 7 ∈ {3, 5, 6}` and
   `p ≢ 0, −1 (mod ℓ)` for every prime `5 ≤ ℓ ≤ L` with `ℓ ≡ 1 (mod 4)`, and `T_L` is the set of primes
   bad at some `ℓ > L`. Its Dirichlet density is at least
   `δ_L − α_L`, where `δ_L ≥ 3/(8(L − 1))` and `α_L ≤ 5.6·A₁/(L log L)`.
4. **The tail is the one deep-ish step** (§4). For `L < ℓ ≤ N^{1/4}` one needs
   `#{p ≤ N bad at ℓ} ≤ A₁N/(ℓ² log N)` uniformly in `ℓ`. I prove it with `A₁ = 16003` by a
   two-dimensional Selberg sieve on the lattice coset `{(ℓU, b + ℓV)}`, with sifting density
   `ν(q) = (2q − 1)/q²` for `q ≡ 1 (mod 4)`. The bound for the Selberg sum `S ≫ log N` is proved by an
   elementary comparison with `Σ r(n)/n` (no Mertens theorem, no `L(1, χ₄)` evaluation). For
   `ℓ > N^{1/4}` a lattice count gives `O(N^{3/4})`. Trivial counting cannot replace the sieve (§4.1),
   and none of the choices of `G*` examined in §4.6 avoids it. PrimeNumberTheoremAnd's `SelbergSieve.selberg_bound_simple`
   (sorry-free, built on Mathlib's `BoundingSieve`) is the closed Selberg bound this needs.
5. **Lean plan** (§6). Nine files: about 2.5–4k new lines plus a 1.5k-line port. That is less than earlier estimates, because the
   CM step shrinks to a few hundred lines of character sums. The hard part is the sieve instance
   (§4.3–4.5). A conditional theorem `goodPrimeDensity_of_uniformBadBound`, with the sieve bound as its
   only hypothesis, isolates it. The first step is Proposition 1.6 in Lean, which removes the most
   specialised piece of the earlier plan.

---

## 0. The target statements

The hypothesis to be discharged is `ZInQ.GoodPrimeAP` (`ZInQKernel/Hypotheses/PrimeAP.lean`). Its
derivation from Green–Tao 2008, Theorem 1.2, is written in `scratch/gt-search/GreenTaoReduction.lean`
(branch `wip/gt-search`; it compiles against our Mathlib, VERIFIED there). That file defines

```lean
def PrimesRelUpperDensityPos (A : Set ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ᶠ N in atTop,
    c * (Nat.primeCounting N : ℝ) ≤ (((Finset.range (N + 1)).filter (· ∈ A)).card : ℝ)
```

and proves `progressions_above_of_greenTaoDense`: if Green–Tao's Theorem 1.2 holds (`GreenTaoDense`), and
`G` consists of primes and satisfies `PrimesRelUpperDensityPos`, then `GoodPrimeAP` holds. So the
statement to prove is

> **Proposition D (weak form).** `PrimesRelUpperDensityPos {p | ZInQ.GoodSlopePrime p}`.

It will be derived from

> **Theorem D.** There is `L` with `liminf_{x→1⁺}(x − 1)·Φ_{G*_L}(x) ≥ η_L > 0`. Since `G*_L ⊆ G`,
> in particular `liminf_{x→1⁺}(x − 1)Φ_G(x) > 0`.

through Proposition 5.3 (Dirichlet density ⇒ upper natural density). Theorem D gives a lower
Dirichlet density in the von Mangoldt normalisation. The classical normalisation
`Σ_{p∈G} p^{−x}/log(1/(x − 1))` is equivalent for this purpose (Remark 5.4). The full Proposition D of
`nt-22p.md` §2.2 (natural density equal to `(1/8)∏_{ℓ≡1 (4)}(1 − 2/(ℓ − 1)²) ≈ 0.1060`) needs Hecke's
theorem for `ℚ(i)`. It is not needed for `GoodPrimeAP` (§3.1).

---

## 1. From the Lean definition to the arithmetic description

### 1.1 The definition

`ZInQ.GoodSlopePrime p` (`ZInQKernel/Hypotheses/PrimePattern.lean`) says: `p` is prime, and there is
`r : ZMod p` with `r² = 2`, `75 − 53r ≠ 0`, `75 + 53r ≠ 0` and

  `Nat.gcd (pointCount p (−(75 − 53r)²)) (pointCount p (−(75 + 53r)²)) = 4`,

where `pointCount p a = Nat.card {(x, y) : ZMod p × ZMod p // y² = x³ + ax} + 1`. VERIFIED (source).
Throughout, `d = 75 − 53r` and `d̄ = 75 + 53r`. Then `dd̄ = 75² − 53²r² = 5625 − 2·2809 = 7`. VERIFIED
(arithmetic).

### 1.2 Four lemmas on character sums

Let `p` be an odd prime.

**Lemma 1.1 (point count).** For every `a ∈ 𝔽_p`, `pointCount p a = p + 1 + φ_p(a)`.

*Proof.* For `c ∈ 𝔽_p` the equation `y² = c` has `1 + χ(c)` solutions (Mathlib
`quadraticChar_card_sqrts`, which needs `ringChar ≠ 2`). Sum over `x` with `c = x³ + ax`. ∎ VERIFIED
(by hand; `scratch/pd-paper/lemmas.py`, check A: 6783 random pairs `(p, a)`, `p < 2·10⁴`, literal count
against the formula, no failure).

**Lemma 1.2 (scaling).** For `k ∈ 𝔽_p^×` and `a ∈ 𝔽_p`, `φ_p(k²a) = χ(k)φ_p(a)`.

*Proof.* Substitute `x = kX`: `(kX)³ + k²a·kX = k³(X³ + aX)` and `χ(k³) = χ(k)`. ∎ VERIFIED (by hand;
check B, 6783 samples).

**Lemma 1.3 (shifted products).** For `α ≠ β` in `𝔽_p`, `Σ_{t∈𝔽_p} χ((t + α)(t + β)) = −1`. For
`α = β` the sum is `p − 1`.

*Proof.* For `t ≠ −β`, `χ((t + α)(t + β)) = χ((t + α)/(t + β))`, since `χ((t + β)²) = 1`. The map
`t ↦ (t + α)/(t + β)` is a bijection from `𝔽_p ∖ {−β}` onto `𝔽_p ∖ {1}` (it is a Möbius map of
determinant `β − α ≠ 0`). So the sum is `Σ_{w≠1} χ(w) = −χ(1) = −1` (Mathlib `quadraticChar_sum_zero`).
For `α = β`, `χ(u²) = 1` for `u ≠ 0`. ∎ VERIFIED (by hand). The same identity is
`jacobiSum χ χ = −χ(−1)` (Mathlib `jacobiSum_nontrivial_inv`) after the substitution
`t = −β + (β − α)w`.

**Lemma 1.4 (Jacobsthal's identity).** Let `p ≡ 1 (mod 4)` and let `r ∈ 𝔽_p` be a non-square. Then
`φ_p(1)` and `φ_p(r)` are even and

  `φ_p(1)² + φ_p(r)² = 4p`.

*Proof.* For `x ≠ 0`, `χ(x³ + ax) = χ(x)χ(x² + a)`. *Evenness:* `x ↦ −x` fixes the summand, because
`χ(−1) = 1`, and its only fixed point `x = 0` contributes `0`. *Second moment:*

  `Σ_{a∈𝔽_p} φ_p(a)² = Σ_{x,y} χ(x)χ(y) Σ_a χ((a + x²)(a + y²))`.

By Lemma 1.3 the inner sum is `p − 1` if `x² = y²` and `−1` otherwise. Hence

  `Σ_a φ_p(a)² = −(Σ_x χ(x))² + p·Σ_{x² = y²} χ(xy) = 0 + p·Σ_{x≠0}(χ(x²) + χ(−x²)) = 2p(p − 1)`.

Here `x² = y²` means `y = ±x`, the pair `x = y = 0` contributes `0`, and `χ(−1) = 1`. *Square classes:*
`φ_p(0) = Σ χ(x³) = Σ χ(x) = 0`. By Lemma 1.2, `φ_p(a)² = φ_p(1)²` for the `(p − 1)/2` nonzero squares
`a`, and `φ_p(a)² = φ_p(r)²` for the `(p − 1)/2` non-squares. So `((p − 1)/2)(φ_p(1)² + φ_p(r)²) =
2p(p − 1)`. ∎ VERIFIED (by hand; check D: every prime `p ≡ 1 (mod 4)` below `2·10⁴`, 1125 primes, no
failure). The identity goes back to Jacobsthal (1907). The argument above is complete, so the citation
(Berndt–Evans–Williams, *Gauss and Jacobi Sums*, Ch. 6) is for orientation only. UNCHECKED (theorem
number).

**Lemma 1.5 (divisibility by 4).** Let `p ≡ 1 (mod 4)` and `D ∈ 𝔽_p^×`. Then `4 | pointCount p (−D²)`.

*Proof.* Put `g(x) = x³ − D²x = x(x − D)(x + D)`. Its three roots are distinct, since `p` is odd and
`D ≠ 0`. Counting the solutions of `y² = g(x)` row by row gives `pointCount p (−D²) = 1 + 3 + 2m`, where
`m = #X` and `X = {x ∈ 𝔽_p^× : g(x) is a nonzero square}`. The map `τ(x) = −D²/x` is an involution of
`𝔽_p^×`, and `g(τx) = (D²/x²)²·g(x)`, so `τ(X) = X`. The fixed points of `τ` are the two roots `±iD` of
`x² = −D²`, where `i² = −1` (such `i` exists because `p ≡ 1 (mod 4)`). Since `g` is odd and
`χ(−1) = 1`, either both fixed points lie in `X` or neither does. An involution has
`#X ≡ #Fix (mod 2)` (Mathlib `Equiv.Perm.card_fixedPoints_modEq`), so `m` is even and
`4 | 4 + 2m`. ∎ VERIFIED (by hand; its consequence `φ_p(1) ≡ 2 (mod 4)` passed check C for 1125
primes). This is the elementary form of "all the two-torsion is rational" (manuscript line 1585).

### 1.3 The description

**Proposition 1.6.** Let `p` be a prime with `p ≡ 1 (mod 8)` and `p mod 7 ∈ {3, 5, 6}`. Put
`c_p = φ_p(1)/2` and `e_p = φ_p(r₀)/2` for a non-square `r₀ ∈ 𝔽_p`. Then:

1. `c_p, e_p ∈ ℤ`, `c_p` is odd, and `p = c_p² + e_p²`.
2. There is `r ∈ 𝔽_p` with `r² = 2`. For every such `r`, `d` and `d̄` are nonzero and
   `{pointCount p (−d²), pointCount p (−d̄²)} = {p + 1 − 2c_p, p + 1 + 2c_p}`.
3. `gcd(p + 1 − 2c_p, p + 1 + 2c_p) = 4·gcd(c_p, p + 1)`.
4. Hence `GoodSlopePrime p ⟺ gcd(c_p, p + 1) = 1`. If an odd prime `ℓ` divides `gcd(c_p, p + 1)`,
   then `e_p² ≡ −1 (mod ℓ)` and `ℓ ≡ 1 (mod 4)`.

*Proof.* (2) `p ≡ 1 (mod 8)` gives a square root of 2 (Mathlib `ZMod.exists_sq_eq_two_iff`).
`dd̄ = 7 ≠ 0` in `𝔽_p`, since `p ≠ 7`. As `p ≡ 1 (mod 4)`, quadratic reciprocity gives
`χ(7) = (p/7) = −1`, because the squares mod 7 are `1, 2, 4` (Mathlib
`ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one`). Choose `i` with `i² = −1`. Then `−d² = (id)²`, so by
Lemma 1.2 `φ_p(−d²) = χ(id)φ_p(1)` and `φ_p(−d̄²) = χ(id̄)φ_p(1)`. Moreover
`χ(id)·χ(id̄) = χ(−dd̄) = χ(7) = −1`. By Lemma 1.1 the two counts are `p + 1 ± φ_p(1)`, one of each sign.

(1) By Lemma 1.5, `4 | p + 1 ± φ_p(1)`. Since `p + 1 ≡ 2 (mod 4)`, `φ_p(1) ≡ 2 (mod 4)`, so `c_p` is odd.
`p = c_p² + e_p²` is Lemma 1.4 divided by 4.

(3) Write `n_∓ = p + 1 ∓ 2c_p` and `g = gcd(n₋, n₊)`. Then `4 | g` by Lemma 1.5. Also `g | n₋ + n₊ =
2(p + 1)`, and `v₂(2(p + 1)) = 2`, so `v₂(g) = 2`. For an odd prime power `ℓ^k`: `ℓ^k | g` iff `ℓ^k`
divides `n₋` and `n₊ − n₋ = 4c_p`, iff `ℓ^k | c_p` and `ℓ^k | p + 1`. As `c_p` is odd,
`gcd(c_p, p + 1)` is odd, and `g = 4·gcd(c_p, p + 1)`.

(4) The first claim follows from (2) and (3), because the definition is existential in `r` and the
count is the same for every root. If `ℓ | c_p` and `ℓ | p + 1`, then `e_p² = p − c_p² ≡ −1 (mod ℓ)`,
so `−1` is a square mod `ℓ` and `ℓ ≢ 3 (mod 4)` (Mathlib `ZMod.exists_sq_eq_neg_one_iff`). ∎
VERIFIED (by hand). Check E of `lemmas.py` compared the literal definition with
"`p ≡ 1 (8)`, `(p/7) = −1`, `gcd(c, p + 1) = 1`" for every odd prime below `2·10⁴` (2261 primes,
`p = 7` treated literally): no mismatch. Check F (`gcdformula.py`) confirmed (2) and (3) for all 806
pairs `(p, r)` with `p < 3·10⁴`: no failure.

**Remarks.**
- For the lower bound only the direction "⇐" of (4) is used, and only for `p` in the stated class.
  The converse inclusion, that every good prime `p > 7` lies in this class, is `nt-22p.md` §2.1. It is
  not needed.
- Classically `c_p = ±a`, where `p = a² + b²` with `a` odd: the Frobenius of `y² = x³ − x` is `±(a + bi)`
  up to a unit. That is how the manuscript argues (lines 1563–1583, record A072: Silverman III.7.4,
  III.8.6, V.2.3.1), and it is Gauss's theorem through quartic Jacobi sums (Ireland–Rosen, *A Classical
  Introduction to Modern Number Theory*, Ch. 18 §4; UNCHECKED theorem number). Proposition 1.6 needs
  neither: since `c_p` is odd and `p = c_p² + e_p²`, it is the odd member of the essentially unique
  representation of `p` as a sum of two squares. Which representation it is does not matter below.
- The Hasse bound is not used. If `n₋ = 0`, (3) still holds, because `gcd(0, n) = n` and the
  computation above is about divisors. In fact `n₋ > 0` follows from `c_p² ≤ p`.

---

## 2. The subset `G*_L`

### 2.1 Definition

Fix `L ≥ 5`. Let `Q_L` be the set of primes `ℓ` with `5 ≤ ℓ ≤ L` and `ℓ ≡ 1 (mod 4)`, put
`M_L = 56·∏_{ℓ∈Q_L} ℓ`, and let `A_L ⊂ (ℤ/M_L)^×` be the set of residues `a` with

- `a ≡ 1 (mod 8)`,
- `a mod 7 ∈ {3, 5, 6}` (the non-squares mod 7),
- `a mod ℓ ∉ {0, −1}` for every `ℓ ∈ Q_L`.

Let `C_L` be the set of primes `p` with `p mod M_L ∈ A_L`. For a prime `ℓ ≡ 1 (mod 4)`, let `Bad_ℓ` be
the set of primes `p` with `p ≡ 1 (mod 8)`, `p mod 7 ∈ {3, 5, 6}`, `ℓ | c_p` and `ℓ | p + 1`. Put
`T_L = ⋃_{ℓ>L, ℓ≡1 (4)} Bad_ℓ` and `G*_L = C_L ∖ T_L`.

**Lemma 2.1.** `G*_L ⊆ G`.

*Proof.* Let `p ∈ G*_L`. Then `p ≡ 1 (mod 8)` and `p mod 7 ∈ {3, 5, 6}`. If an odd prime `ℓ` divides
`gcd(c_p, p + 1)`, then `ℓ ≡ 1 (mod 4)` by Proposition 1.6(4), so `ℓ ≥ 5`. If `ℓ ≤ L`, then `ℓ ∈ Q_L`
and `p ≢ −1 (mod ℓ)`, a contradiction. If `ℓ > L`, then `p ∈ Bad_ℓ ⊆ T_L`, again a contradiction. So
`gcd(c_p, p + 1) = 1`, and Proposition 1.6(4) gives `GoodSlopePrime p`. ∎ VERIFIED (by hand).

Three remarks on the choice.

1. **No condition at `ℓ ≡ 3 (mod 4)`, and in particular none at 3 or 7 beyond `(p/7) = −1`.** Such
   primes never divide `gcd(c_p, p + 1)` (Proposition 1.6(4)). The manuscript imposes `p ≢ −1 (mod ℓ)`
   at every odd `ℓ ≤ L` (lines 1384–1390), because it does not use this fact before the bad-value count.
   VERIFIED (by hand; `density.py` found no bad `ℓ ≡ 3 (mod 4)` among the primes below `10⁸`).
2. **`p ≢ −1 (mod ℓ)` rather than `p ≡ 1 (mod ℓ)`.** A single residue class mod `M_L` would have density
   `1/φ(M_L)`, which decays exponentially in `L`, while the tail (§4) decays only like `1/(L log L)`. So
   the whole set `A_L` is needed. The excluded class `0` only removes the prime `ℓ` itself; it makes
   every element of `A_L` a unit.
3. **Density of the main term.** By the Chinese remainder theorem, `|A_L| = 1·3·∏_{ℓ∈Q_L}(ℓ − 2)` and
   `φ(M_L) = 4·6·∏_{ℓ∈Q_L}(ℓ − 1)`. So

   `δ_L := |A_L|/φ(M_L) = (1/8)∏_{ℓ∈Q_L}(ℓ − 2)/(ℓ − 1) ≥ (1/8)∏_{n=5}^{L}(n − 2)/(n − 1) = 3/(8(L − 1))`,

   since every factor is at most 1 and the product over all `5 ≤ n ≤ L` telescopes. VERIFIED (by hand).
   The crude bound is enough below. Mertens' theorem would give `δ_L ≍ (log L)^{−1/2}`.

### 2.2 Numerical check

`scratch/pd-paper/density.py` (all primes up to `N = 10⁸`; output `density_1e8.out`) gives:

| Set | Share of all primes `≤ 10⁸` | Prediction |
| --- | --- | --- |
| `p ≡ 1 (8)`, `(p/7) = −1` | 0.12508 | `1/8` |
| `G` | 0.10612 | `(1/8)∏_{ℓ≡1 (4)}(1 − 2/(ℓ − 1)²) = 0.10602` |
| `G*_5` | 0.09095 | `δ_5·∏_{ℓ>5}(1 − 2/(ℓ − 1)²) = 0.09088` (`δ_5 = 0.09375`) |
| `G*_13` | 0.08456 | 0.08448 (`δ_13 = 0.08594`) |
| `G*_50` | 0.07342 | 0.07335 (`δ_50 = 0.07364`) |
| `G*_100` | 0.06845 | 0.06840 (`δ_100 = 0.06852`) |
| `G*_1000` | 0.05661 | 0.05657 (`δ_1000 = 0.05658`) |

The share of primes of the class that are bad at some `ℓ > 13`, `> 50`, `> 100` is `0.00212`,
`0.00048`, `0.00022` of all primes. The heuristic `Σ_{ℓ>L, ℓ≡1 (4)} 2/(8(ℓ − 1)²)` predicts `0.00214`,
`0.00049`, `0.00022`. Individual counts `|Bad_ℓ ∩ [1, 10⁸]|` agree with `2|C|/(ℓ − 1)²`, for example
89880 against 90080 at `ℓ = 5`, and 140 against 144 at `ℓ = 101`. VERIFIED (computation). The prediction
column uses Hecke equidistribution (§3.1) and is not proved here. The proof below gives only the much
weaker lower bound `δ_L − α_L` for large `L`.

### 2.3 Frobenius conditions and `ℚ`-classes

The conditions defining `C_L` are Frobenius conditions in `ℚ(ζ_{M_L})`. Since this field is abelian,
every condition set is a union of conjugacy classes, hence of `ℚ`-classes. The field suggested in the
task, the Galois closure `K₁ = ℚ(√2, √d, √d̄)` of `ℚ(√d)` (with `d = 75 − 53√2`), has degree 8 and group
`D₄`. Indeed, `d` is not a square in `ℚ(√2, √7)`: writing `d = (u + v√7)²` with `u, v ∈ ℚ(√2)` forces
`uv = 0`; then either `d` or `d/7` is a square in `ℚ(√2)`, but their norms `7` and `1/7` are not rational
squares. VERIFIED (by hand). `K₁` contains `√7 = ±√d·√d̄`. The condition used, "`p` splits in
`ℚ(√2)` and `d, d̄` have opposite quadratic characters mod the primes above `p`", is "`p ≡ ±1 (mod 8)` and
`(7/p) = −1`". It is pulled back from the abelian quotient `Gal(ℚ(√2, √7)/ℚ)`, hence a union of
conjugacy classes of `D₄`. Adding `p ≡ 1 (mod 4)` (the field `ℚ(i)`) gives the class mod 56. The finer
condition "`d` is a square mod `𝔭`" (a non-abelian condition in `K₁`) plays no role, because the gcd
only sees the product `dd̄ = 7` (Proposition 1.6(2)).

---

## 3. The lower bound for `C_L`

### 3.1 Three routes

**(i) Chebotarev, or Hecke for `ℚ(i)`.** This is needed only for the exact density of `G`. The bad
events at `ℓ` are conditions on a Gaussian prime `ϖ` modulo `ℓ` (`nt-22p.md` §2.1). Their independence
and density `2/(ℓ − 1)²` come from Hecke's equidistribution of prime ideals in ray classes of `ℚ(i)`.
STANDARD (Hecke 1920; Narkiewicz, *Elementary and Analytic Theory of Algebraic Numbers*, Ch. 7; exact
theorem numbers UNCHECKED). Neither Mathlib nor PrimeNumberTheoremAnd has it. Mathlib has no Hecke
`L`-functions. In PrimeNumberTheoremAnd the Chebotarev material is blueprint prose
(`Wiener.lean`, section "The Chebotarev density theorem: the case of cyclotomic extensions", and
`Consequences.lean:2537`). VERIFIED (grep of tag `v4.34.0`). Not needed here.

**(ii) Dirichlet density through Dedekind zeta functions and Artin induction.** Let `K/ℚ` be Galois with
group `Γ`, and let `C ⊆ Γ` be a union of `ℚ`-classes (closed under conjugation and under `σ ↦ σ^k` for
`k` prime to the order of `σ`). By Artin's induction theorem, `1_C` is a `ℚ`-linear combination
`Σ_H a_H Ind_H^Γ 1` over cyclic subgroups `H`. Then
`Σ_{p : Frob_p ∈ C} p^{−s} = Σ_H a_H log ζ_{K^H}(s) + O(1)`. Each `ζ_{K^H}` has a simple pole at `s = 1`,
so `log ζ_{K^H}(s) = log(1/(s − 1)) + O(1)` as `s → 1⁺`, with no zero-free region needed. Hence `C` has
Dirichlet density `Σ_H a_H = |C|/|Γ|`. STANDARD (Frobenius's density theorem; Artin induction: Serre,
*Linear Representations of Finite Groups*, §9.2; theorem number UNCHECKED). What Mathlib has:

- the simple pole and its residue: `NumberField.dedekindZeta`, `NumberField.dedekindZeta_residue`,
  `NumberField.dedekindZeta_residue_pos`, `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT`
  (`(s − 1)ζ_K(s) → residue` as `s → 1⁺`, the class number formula) (`NumberTheory/NumberField/DedekindZeta.lean`);
- Dirichlet density of sets of primes of a number field: `NumberField.Set.primeIdealZetaSum`,
  `HasDirichletDensity`, `dirichletDensity`, with basic lemmas only (empty set, `0 ≤ δ ≤ 1`, finite
  sets) (`NumberField/DirichletDensity.lean`);
- Frobenius elements: `AlgHom.IsArithFrobAt` and `IsArithFrobAt.exists_of_isInvariant`
  (`RingTheory/Frobenius.lean`); for cyclotomic fields `IsCyclotomicExtension.autEquivPow`
  (`Gal ≃* (ZMod n)ˣ`) and `galEquivZMod`, `mem_zpowers_galEquivZMod_of_mem_stabilizer`
  (`NumberField/Cyclotomic/Galois.lean`).

What it lacks: the Euler product of `ζ_K` (so `log ζ_K = Σ_𝔭 N𝔭^{−s} + O(1)`), the splitting of `p` in
`K^H` in terms of Frobenius classes, and Artin's induction theorem. VERIFIED (grep). This route would be
needed for a genuinely non-abelian condition. Section 2.3 shows that there is none here.

**(iii) Dirichlet's theorem for residue classes.** This is route (ii) for `K = ℚ(ζ_M)`. Mathlib has it
in the needed form:

> `ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound {q : ℕ} [NeZero q] {a : ZMod q}
> (ha : IsUnit a) : ∃ C : ℝ, ∀ {x : ℝ} (_ : x ∈ Set.Ioc 1 2),
> (q.totient : ℝ)⁻¹ / (x − 1) − C ≤ ∑' n, residueClass a n / (n : ℝ) ^ x`

with `residueClass a = {n | (n : ZMod q) = a}.indicator Λ` (`NumberTheory/LSeries/PrimesInAP.lean:348`),
and `summable_residueClass_non_primes_div` (line 181) for the prime powers. VERIFIED (source). Natural
density would need the prime number theorem in progressions, PrimeNumberTheoremAnd `WeakPNT_AP`
(`Wiener.lean:4025`). That file contains two `sorry`s (lines 327 and 347). VERIFIED (grep). Whether
`WeakPNT_AP` depends on them is UNCHECKED (`gt-search.md` §4 found by a static grep that it does not).
Dirichlet density avoids the question.

**Choice: route (iii).**

### 3.2 The main term

**Lemma 3.1.** For every `L ≥ 5` there is `K_L` such that `Φ_{C_L}(x) ≥ δ_L/(x − 1) − K_L` for all
`x ∈ (1, 2]`.

*Proof.* Every `a ∈ A_L` is a unit mod `M_L`. Summing `LSeries_residueClass_lower_bound` over `a ∈ A_L`
gives `Σ_{n mod M_L ∈ A_L} Λ(n)/n^x ≥ |A_L|/(φ(M_L)(x − 1)) − Σ_a C_a`. A prime `p` lies in `C_L` iff
`p mod M_L ∈ A_L`, so the left side is `Φ_{C_L}(x)` plus a contribution of prime powers `p^k`, `k ≥ 2`.
That contribution is at most `K₀ = Σ_p Σ_{k≥2} log p/p^k = Σ_p log p/(p(p − 1)) < 1` (numerically
`0.7554`). Mathlib's `summable_residueClass_non_primes_div` gives its finiteness, class by class. Put
`K_L = K₀ + Σ_a C_a`. ∎ VERIFIED (by hand, against the Mathlib statement). The count `|A_L|/φ(M_L) = δ_L`
is the Chinese remainder theorem: Mathlib `ZMod.prodEquivPi` (`ZMod (∏ aᵢ) ≃+* Π ZMod aᵢ` for pairwise
coprime `aᵢ`), `ZMod.chineseRemainder`, `Nat.totient_mul`, `Nat.totient_prime`.

---

## 4. The primes removed at `ℓ > L`

### 4.1 What is needed, and why trivial counting fails

Theorem D needs `θ_{T_L}(N) ≤ α_L N + o(N)`, with `α_L < δ_L`. Two naive bounds fail.

- *Using `p ≡ −1 (mod ℓ)` alone.* Then `#(Bad_ℓ ∩ [1, N]) ≤ π(N; ℓ, −1) ≈ π(N)/(ℓ − 1)`. The sum over
  `L < ℓ ≤ N^θ` is about `π(N)·log(θ log N/log L)`, which is unbounded relative to `π(N)`. The bad
  event has density `≍ 1/ℓ²` only through the joint condition on `(c_p, p)`.
- *Counting lattice points instead of primes.* This gives `#(Bad_ℓ ∩ [1, N]) ≤ 8N/ℓ² + …`
  (Proposition 4.1), and `Σ_{ℓ>L} 8N/ℓ² ≍ N/(L log L)`. For fixed `L` this is not `O(π(N))` with a small
  constant: it lacks the factor `1/log N`. The same loss occurs in Dirichlet-series form:
  `Σ_{α ≡ β (mod ℓ)} N(α)^{−x} ≈ (π/ℓ²)/(x − 1)`, against `Σ_p p^{−x} ≈ log(1/(x − 1))`.

So for `L < ℓ ≤ N^θ` one needs `#(Bad_ℓ ∩ [1, N]) ≤ A₁N/(ℓ² log N)` uniformly in `ℓ`. This is
`rv-nt22p-ap` F5. VERIFIED (by hand).

### 4.2 Large `ℓ`: a lattice count

For an odd prime `ℓ ≡ 1 (mod 4)`, let `b_ℓ ∈ (0, ℓ)` be one root of `b² ≡ −1 (mod ℓ)`; the other root is
`ℓ − b_ℓ`.

**Proposition 4.1.** For every `N` and every prime `ℓ ≡ 1 (mod 4)`:

  `#(Bad_ℓ ∩ [1, N]) ≤ 8N/ℓ² + 4√N/ℓ`, and this count is `0` if `ℓ > √N`.

Consequently, for `N ≥ 10³`, `Σ_{ℓ > N^{1/4}} #(Bad_ℓ ∩ [1, N]) ≤ 20N^{3/4}`.

*Proof.* Let `p ∈ Bad_ℓ`, `p ≤ N`. By Proposition 1.6, `p = c_p² + e_p²` with `c_p` odd, hence nonzero,
`ℓ | c_p`, and `e_p² ≡ −1 (mod ℓ)`, so `e_p ≡ ±b_ℓ (mod ℓ)`. The map `p ↦ (c_p, e_p)` is injective.
Write `c_p = ℓU` with `1 ≤ |U| ≤ √N/ℓ`: at most `2√N/ℓ` choices, and none if `ℓ > √N`. For `e_p` there
are at most `2(2√N/ℓ + 1)` choices in `[−√N, √N]` in the two classes. Multiply. For the sum, use
`Σ_{n > X} 8N/n² ≤ 8N/(X − 1)` with `X = N^{1/4} ≥ 2`, and `Σ_{n ≤ √N} 4√N/n ≤ 4√N(1 + log √N)`.
Finally, `16N^{3/4} + 4√N(1 + (1/2)log N) ≤ 20N^{3/4}` for `N ≥ 10³`. ∎ VERIFIED (by hand; the
manuscript has the same count at lines 1626–1636, with the term `√X log X` noted by `rv-nt22p-ap` F5).
Numerically, 1250 primes of the class below `10⁸` are bad at some `ℓ > 100 = N^{1/4}`, against the bound
`20N^{3/4} = 2·10⁷` (`density_1e8.out`).

### 4.3 Medium `ℓ`: the sieve set-up

**Proposition 4.2 (uniform bound).** Let `N ≥ N₁ := e^{1920}`, and let `ℓ ≡ 1 (mod 4)` be a prime with
`5 ≤ ℓ ≤ N^{1/4}`. Then `#(Bad_ℓ ∩ [1, N]) ≤ A₁N/(ℓ² log N)` with `A₁ = 16003`.

The constants are far from optimal: `density.py` gives `max |Bad_ℓ ∩ [1, N]|·ℓ² log N/N ≈ 0.30` for
`13 < ℓ ≤ N^{1/4}`, `N = 10⁸`. They are chosen so that every step is a one-line inequality.

*Set-up.* Fix `ℓ` and a root `b ∈ {b_ℓ, ℓ − b_ℓ}`. Put `T = √N`, `K = ⌊T/ℓ⌋`, `I₁ = [−K, K] ∩ ℤ` and
`I₂ = {V ∈ ℤ : |b + ℓV| ≤ T}`. Both are intervals of integers, with `M₁ = |I₁| ≤ 2T/ℓ + 1` and
`M₂ = |I₂| ≤ 2T/ℓ + 1`. Put `ℬ = I₁ × I₂` and `F(U, V) = (ℓU)² + (b + ℓV)² ∈ ℕ`. Every
`p ∈ Bad_ℓ ∩ [1, N]` with `e_p ≡ b (mod ℓ)` equals `F(U, V)` for `(U, V) = (c_p/ℓ, (e_p − b)/ℓ) ∈ ℬ`, and
distinct `p` give distinct points.

*Sieve data* (Mathlib `BoundingSieve`, `SelbergSieve`):

- `support = F(ℬ)` (a `Finset ℕ`), `weights n = #{(U, V) ∈ ℬ : F(U, V) = n}`, `totalMass X = M₁M₂`;
- `prodPrimes P = ∏{q prime : q ≤ w, q ≡ 1 (mod 4), q ≠ ℓ}` with `w = N^{1/40}`; `level y = w² = N^{1/20}`;
- `nu ν`, multiplicative, with `ν(q) = (2q − 1)/q²` for `q | P`, so `0 < ν(q) < 1`.

`multSum d = #{(U, V) ∈ ℬ : d | F(U, V)}`, and `siftedSum` counts the points with `gcd(F(U, V), P) = 1`.
If `F(U, V) = p` is a prime `> w`, the point is counted. So

  `#{p ∈ Bad_ℓ ∩ [1, N] : e_p ≡ b} ≤ siftedSum + w`.   (4.1)

**Lemma 4.3 (local densities).** Let `q ≡ 1 (mod 4)` be a prime, `q ≠ ℓ`. Then
`#{(U, V) ∈ 𝔽_q² : F(U, V) = 0} = 2q − 1`. For squarefree `d | P`, by the Chinese remainder theorem,
`ρ(d) := #{(U, V) ∈ (ℤ/d)² : d | F(U, V)} = ∏_{q|d}(2q − 1) = ν(d)d²`.

*Proof.* `(U, V) ↦ (ℓU, b + ℓV)` is a bijection of `𝔽_q²`, since `ℓ` is invertible mod `q`. With
`i² = −1` in `𝔽_q`, `x² + y² = (x − iy)(x + iy)` vanishes exactly on two lines that meet only at `0`:
`2q − 1` points. ∎ VERIFIED (by hand). This is the manuscript's computation at lines 1610–1614.

**Lemma 4.4 (remainders).** For squarefree `d | P`, `multSum d = ν(d)X + R_d` with
`|R_d| ≤ ρ(d)((M₁ + M₂)/d + 1) ≤ 2^{ω(d)}(M₁ + M₂ + d)`.

*Proof.* For each of the `ρ(d)` residue pairs `(u, v)`, `#{U ∈ I₁ : U ≡ u (mod d)} = M₁/d + θ₁` and
`#{V ∈ I₂ : V ≡ v} = M₂/d + θ₂` with `|θᵢ| ≤ 1`. The product is
`M₁M₂/d² + θ₁M₂/d + θ₂M₁/d + θ₁θ₂`. Sum over the pairs, and use `ρ(d) ≤ ∏_{q|d} 2q = 2^{ω(d)}d`. ∎
VERIFIED (by hand).

### 4.4 The Selberg bound and the error terms

PrimeNumberTheoremAnd (`Mathlib/NumberTheory/Sieve/Selberg.lean:435`, tag `v4.34.0`) proves

> `SelbergSieve.selberg_bound_simple : siftedSum ≤ X / S + ∑ d ∈ divisors P,
> if (d : ℝ) ≤ y then 3 ^ ω d * |R d| else 0`,

where `S = selbergBoundingSum = Σ_{l | P, l² ≤ y} g(l)`, and `g = selbergTerms` is multiplicative with
`g(q) = ν(q)/(1 − ν(q))`. VERIFIED (source read; the file and its three companions contain no `sorry`;
they import Mathlib's `NumberTheory/SelbergSieve.lean`, which has the definitions and
`siftedSum_le_mainSum_errSum_of_upperMoebius`, `upperMoebius_lambdaSquared`,
`mainSum_lambdaSquared_eq_sum_mul_sum_sq`, but no closed bound). The supporting lemmas there are
`selberg_bound_weights` (`|γ d| ≤ 1`), `selberg_bound_muPlus` and `selberg_bound_simple_errSum`.

*Error term.* For `d | P` all prime factors are `≥ 5`, so `3^{ω(d)}2^{ω(d)} ≤ d²`. By Lemma 4.4,

  `Σ_{d|P, d≤y} 3^{ω(d)}|R_d| ≤ y³(M₁ + M₂ + y)`.

Since `ℓ ≤ N^{1/4}`, `T/ℓ ≥ N^{1/4} ≥ max(2, y)`, so `M₁ + M₂ + y ≤ 6T/ℓ`, and the error is at most
`6N^{3/20}√N/ℓ = (N/(ℓ² log N))·6ℓN^{−7/20} log N ≤ (N/(ℓ² log N))·6N^{−1/10} log N`. This is at most
`N/(ℓ² log N)` once `N ≥ 10³⁰`. VERIFIED (by hand).

*Total mass.* `X = M₁M₂ ≤ (2T/ℓ + 1)² ≤ (4N/ℓ²)(1 + N^{−1/4}/2)² ≤ 5N/ℓ²` for `N ≥ 324`.

### 4.5 The lower bound for the Selberg sum

**Lemma 4.5.** For `w ≥ 3` and every prime `ℓ ≥ 5`: `S ≥ ((2/3)log w − 2)/25`.

*Proof.* `g(q) = (2q − 1)/(q − 1)² ≥ 2/q`. Since `y = w²`, the condition `l² ≤ y` means `l ≤ w`. Let `𝒟`
be the set of squarefree numbers all of whose prime factors are `≡ 1 (mod 4)`. Every `l ∈ 𝒟` with
`l ≤ w` and `ℓ ∤ l` divides `P`. Hence `S ≥ S₀(w; ℓ) := Σ_{l∈𝒟, l≤w, ℓ∤l} 2^{ω(l)}/l`. The terms with
`ℓ | l` contribute at most `(2/ℓ)S₀(w)`, where `S₀(w) = Σ_{l∈𝒟, l≤w} 2^{ω(l)}/l`. So
`S₀(w; ℓ) ≥ (3/5)S₀(w)`. The lemma follows from Claims A and B below with `V < 15`:
`S ≥ (3/5)·((2/3)log w − 2)/15`. ∎

Let `χ₄` be the non-principal character mod 4, `r(n) = Σ_{d|n} χ₄(d)` and `R(w) = Σ_{n≤w} r(n)/n`.

*Claim A.* `R(w) ≥ (2/3)log w − 2` for `w ≥ 3`.

*Proof.* `R(w) = Σ_{d≤w} (χ₄(d)/d)H(w/d)`, where `H(t) = Σ_{m≤t} 1/m`. For `t ≥ 1` and `n = ⌊t⌋`,
`H_n − log(n + 1) < γ < H_n − log n` (Mathlib `eulerMascheroniSeq_lt_eulerMascheroniConstant` and
`eulerMascheroniConstant_lt_eulerMascheroniSeq'`). So `H(t) = log t + γ + E(t)` with
`|E(t)| ≤ 1/n ≤ 2/t`. Then

  `R(w) = S₁ log w − S₂ + γS₁ + Σ_{d≤w} χ₄(d)E(w/d)/d`,

with `S₁ = Σ_{d≤w} χ₄(d)/d ∈ [2/3, 1]` and `S₂ = Σ_{d≤w} χ₄(d)(log d)/d ∈ [−(log 3)/3, 0]`. Both are
partial sums of alternating series with decreasing terms; the first term of `S₂` is `0`, and
`(log x)/x` decreases for `x ≥ 3`. The last sum is at most `Σ_{d≤w} 2/w ≤ 2` in absolute value. ∎
VERIFIED (by hand; `sieveaux.py`: `R(10⁶) = 11.50 ≥ 7.21`).

*Claim B.* `R(w) ≤ V·S₀(w)`, where `V = Σ_{m≥1} v(m)/m ≤ 2ζ(2)⁴ < 15`, for the multiplicative `v`
defined by: `v(2^a) = 1`; for `q ≡ 3 (mod 4)`, `v(q^{2b}) = 1` and `v(q^{2b+1}) = 0`; for `q ≡ 1 (mod 4)`,
`v(q^{2j}) = 2j + 1` and `v(q^{2j+1}) = 0`.

*Proof.* Let `h = 2^ω·1_𝒟`. Pointwise `r ≤ h ∗ v`: both sides are multiplicative and nonnegative, and
on prime powers the two agree except for `q ≡ 1 (4)` with `k = 2j + 1` odd, where
`r(q^k) = k + 1 ≤ 2k = (h ∗ v)(q^k)`. Hence
`R(w) ≤ Σ_{m≤w} (v(m)/m)·Σ_{l≤w/m} h(l)/l ≤ V·S₀(w)`. For the bound on `V`: `v` vanishes off
`m = 2^a s²` with `s` odd, and `v(2^a s²) ≤ τ(s²) ≤ τ(s)²`. Moreover
`Σ_s τ(s)²/s² = Σ_{d,e} Σ_{lcm(d,e) | s} s^{−2} ≤ ζ(2)·Σ_{d,e} lcm(d, e)^{−2} ≤ ζ(2)⁴`, by writing
`d = gd′`, `e = ge′`. With the factor `Σ_a 2^{−a} = 2`, `V ≤ 2ζ(2)⁴ = 14.64`. ∎ VERIFIED (by hand;
`sieveaux.py`: `r ≤ h ∗ v` for `n < 3000`; partial sums of `V` reach `2.74`; `S₀(10⁶) = 4.74`).

*Proof of Proposition 4.2.* Take `w = N^{1/40}`. For `log N ≥ 1920`, Lemma 4.5 gives
`S ≥ (log N/60 − 2)/25 ≥ log N/1600`. The Selberg bound, §4.4 and (4.1) give, for each of the two roots
`b`, `siftedSum ≤ (5N/ℓ²)(1600/log N) + N/(ℓ² log N) = 8001N/(ℓ² log N)`. So
`#(Bad_ℓ ∩ [1, N]) ≤ 16002N/(ℓ² log N) + 2N^{1/40} ≤ 16003N/(ℓ² log N)`, because
`N/(ℓ² log N) ≥ √N/log N ≥ 2N^{1/40}`. ∎ VERIFIED (by hand), given `selberg_bound_simple`.

### 4.6 Can a cleverer `G*` avoid the sieve?

I looked for a subset of `G` whose density can be bounded below without a uniform upper bound at large
`ℓ`. None of the following works.

- *Finitely many Chebotarev conditions.* No condition in a fixed number field implies
  `gcd(c_p, p + 1) = 1`. The events at different `ℓ` are independent (`nt-22p.md` §2.4, "No finite
  version"), so any Chebotarev class contains a positive proportion of primes that are bad at some
  larger `ℓ`. This is SPECULATIVE in the strict sense: it rests on Hecke equidistribution, which is not
  proved here. It is consistent with `density.py`.
- *Conditions on `p` alone* (`p ≢ −1 (mod ℓ)` for more `ℓ`, or `(p + 1)/2` with few prime factors).
  Removing `p ≡ −1 (mod ℓ)` for all `ℓ ≤ N^θ` is itself a sieve, of the lower-bound kind, on primes, which
  is harder. Asking `(p + 1)/2` to be prime or smooth leaves a set of density zero, or of unknown
  density.
- *Conditions on `c_p`.* `c_p mod m` is a Frobenius condition in a ray class field of `ℚ(i)`. It is not a
  congruence on `p`, so controlling it requires Hecke. A restriction such as `|c_p| < L` has density
  zero.
- *Weaker density notions.* Upper density "for infinitely many `N`" does not help: the bad count must
  still be summed over `ℓ` at a single `N`. Dirichlet density does not help either (§4.1).
- *Brun's pure sieve* reaches only `z = (log N)^{O(1)}` and saves `1/log log N`, so the sum over `ℓ` is
  about `N/(L log log N)`, which is not `o(π(N))`.

What can replace the Selberg sieve, at equal or greater cost:

- a Brun–Titchmarsh theorem for prime ideals of `ℚ(i)` in ray classes mod `ℓ`, uniform in `ℓ` (for
  example Hinz–Lodemann, *On Siegel zeros of Hecke–Landau zeta-functions*, Monatsh. Math. 118 (1994);
  UNCHECKED, statement from memory), whose proof is a Selberg sieve in `ℤ[i]`;
- the arithmetic large sieve in two dimensions;
- a one-dimensional Selberg sieve in `e` for each fixed `U`. Here the density `ν_U(q) = #{e : e² ≡ −ℓ²U²}/q`
  depends on `U`, so the bound for `S` must be averaged over `U`, which is more work than §4.5.

Conclusion: an upper-bound sieve of dimension 1 (two-dimensional, sifting density `≈ 2/q` on half the
primes) at level `N^δ` is the minimal input. This is how the manuscript argues (lines 1600–1642). VERIFIED
in the sense that every alternative above fails for the stated reason. SPECULATIVE that no other choice
exists.

---

## 5. Assembly

**Lemma 5.1 (prime tail).** For `L ≥ 2`, `Σ_{ℓ>L} 1/ℓ² ≤ 4 log 4/(L log L)`.

*Proof.* `Σ_{ℓ>L} ℓ^{−2} ≤ (log L)^{−1} Σ_{k≥0} Σ_{2^kL<ℓ≤2^{k+1}L} (log ℓ)/ℓ²
≤ (log L)^{−1} Σ_k θ(2^{k+1}L)/(4^kL²) ≤ (log L)^{−1} Σ_k (log 4)·2^{k+1}/(4^kL)`, by Mathlib
`Chebyshev.theta_le_log4_mul_x`. ∎ VERIFIED (by hand; `sieveaux.py` for `L = 10, …, 10⁴`).

**Lemma 5.2 (Abel summation).** Let `S` be a set of primes and `x > 1`.

1. If `θ_S(n) ≤ κn + βn^{3/4} log n` for all `n ≥ n₀`, then
   `(x − 1)Φ_S(x) ≤ κx² + (x − 1)C(S, n₀, β)`, for a constant `C(S, n₀, β)` independent of `x ∈ (1, 2]`.
2. Hence, if `#(S ∩ [1, N]) ≤ αN/log N + βN^{3/4}` for all `N ≥ N₀`, then
   `limsup_{x→1⁺}(x − 1)Φ_S(x) ≤ α`.

*Proof.* Let `a_n = log n·1_S(n)`. Discrete partial summation (Mathlib `Finset.sum_range_by_parts`)
gives `Σ_{n≤M} a_n n^{−x} = θ_S(M)M^{−x} + Σ_{n<M} θ_S(n)(n^{−x} − (n + 1)^{−x})`. Use
`n^{−x} − (n + 1)^{−x} ≤ x n^{−x−1}`, `Σ_{n≥1} n^{−x} ≤ x/(x − 1)` and
`Σ_n n^{−1/4−x} log n ≤ Σ_n n^{−5/4} log n < ∞`; the terms `n < n₀` give a constant. Let `M → ∞`.
(2) follows from (1), since `θ_S(N) ≤ #(S ∩ [1, N])·log N`. ∎ VERIFIED (by hand).

**Proposition 5.3 (Dirichlet density ⇒ upper natural density).** Let `S` be a set of primes with
`liminf_{x→1⁺}(x − 1)Φ_S(x) ≥ η > 0`. Then `θ_S(N) > κN` for infinitely many `N`, for every `κ < η`. Hence
`PrimesRelUpperDensityPos S` holds with every `c < η/log 4`.

*Proof.* If `θ_S(n) ≤ κn` for all `n ≥ n₀` with `κ < η`, Lemma 5.2(1) (with `β = 0`) gives
`limsup (x − 1)Φ_S(x) ≤ κ < η`, a contradiction. For such `N`, `#(S ∩ [1, N]) ≥ θ_S(N)/log N > κN/log N`.
By Chebyshev, `π(N) ≤ (log 4 + ε)N/log N` for large `N` (Mathlib `Chebyshev.eventually_primeCounting_le`).
So `#(S ∩ [1, N]) ≥ (κ/(log 4 + ε))·π(N)` infinitely often. ∎ VERIFIED (by hand).

*Remark 5.4.* With the classical normalisation, the lower Dirichlet density
`δ⁻(S) = liminf_{x→1⁺} Σ_{p∈S} p^{−x}/Σ_p p^{−x}` is at most the upper relative density
`limsup #(S ∩ [1, N])/π(N)`, by the same Abel summation with `π(t)` in place of `θ(t)`. STANDARD (for
example Serre, *A Course in Arithmetic*, VI.4.5; exact location UNCHECKED). The von Mangoldt
normalisation is the one that matches `LSeries_residueClass_lower_bound`, and it avoids `log(1/(x − 1))`.

**Theorem D.** Let `L ≥ 5` with `log L ≥ 15A₁` (`A₁ = 16003`). Then
`liminf_{x→1⁺}(x − 1)Φ_{G*_L}(x) ≥ η_L := δ_L − α_L > 0`, where `α_L = A₁Σ_{ℓ>L} ℓ^{−2}`. Consequently
(Lemma 2.1 and Proposition 5.3), `G` satisfies `PrimesRelUpperDensityPos` with every `c < η_L/log 4`.

*Proof.* For `N ≥ max(N₁, L⁴)`, Proposition 4.2 for `L < ℓ ≤ N^{1/4}` and Proposition 4.1 for
`ℓ > N^{1/4}` give `#(T_L ∩ [1, N]) ≤ α_L N/log N + 20N^{3/4}`. By Lemma 5.2(2),
`limsup (x − 1)Φ_{T_L}(x) ≤ α_L`. Since `G*_L ⊇ C_L ∖ T_L`, `Φ_{G*_L} ≥ Φ_{C_L} − Φ_{T_L}`, and Lemma 3.1
gives `liminf (x − 1)Φ_{G*_L}(x) ≥ δ_L − α_L`. Finally, `δ_L ≥ 3/(8(L − 1)) > 3/(8L)` (§2.1, remark 3)
and `α_L ≤ 4(log 4)A₁/(L log L) < 5.55A₁/(L log L)` (Lemma 5.1). Their difference is positive when
`log L > 14.8A₁`. ∎ VERIFIED (by hand), given the cited Mathlib and PrimeNumberTheoremAnd statements.

*Remarks.*
- The constant is absurd (`L ≈ e^{240045}`), but only `η_L > 0` enters `GoodPrimeAP`. With Mertens'
  theorem (`δ_L ≍ (log L)^{−1/2}`) and an optimised sieve (true constant about `0.25`, §4.3) one could take
  `L` of size about 50, as the table of §2.2 suggests. This is not needed.
- Replacing Lemma 3.1 by the prime number theorem in progressions (`WeakPNT_AP`) turns the same argument
  into a positive lower natural density `liminf #(G ∩ [1, N])/π(N) ≥ η_L`. Adding Hecke's theorem gives
  the exact density `0.1060…` of `nt-22p.md` §2.2.
- Only the inclusion `G*_L ⊆ G` is used. Nothing depends on the converse description of `G`.

---

## 6. A Lean plan

### 6.1 Files and statements

The plan adds a directory `ZInQKernel/Density/` and a vendored `ZInQKernel/Sieve/`. No existing file
changes, except that the final link replaces the hypothesis `GoodPrimeAP` by `GreenTaoDense`. Names are
proposals; `χ = quadraticChar (ZMod p)`. Line counts are estimates, not measurements.

| # | File | Content (section of this note) | Lines |
| --- | --- | --- | --- |
| 1 | `Density/CharSum.lean` | `jac a = Σ_x χ(x³ + ax)`; Lemmas 1.1–1.5 | 300–450 |
| 2 | `Density/Description.lean` | `InClass`, `cp`, `ep`; Proposition 1.6 | 200–300 |
| 3 | `Density/Abel.lean` | `PhiS`; Lemma 5.2, Proposition 5.3 | 250–400 |
| 4 | `Density/Residues.lean` | `A_L`, CRT count, `δ_L ≥ 3/(8(L − 1))`, Lemma 3.1 | 250–400 |
| 5 | `Density/PrimeTail.lean` | Lemma 5.1 | 100–200 |
| 6 | `Density/Lattice.lean` | Proposition 4.1 | 200–300 |
| 7 | `Sieve/{Basic,AuxResults,Selberg,SelbergBounds}.lean` | PrimeNumberTheoremAnd `v4.34.0`, ported to Lean 4.35 / Mathlib `56a00585` | 1536 existing |
| 8 | `Density/GaussSieve.lean` | Lemmas 4.3–4.5, Claims A and B, Proposition 4.2 | 900–1500 |
| 9 | `Density/PropD.lean` | Theorem D; the conditional and unconditional Proposition D | 150–250 |

Key statements:

```lean
namespace ZInQ.Density
-- File 1
noncomputable def jac {p : ℕ} [Fact p.Prime] (a : ZMod p) : ℤ :=
  ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x)
theorem pointCount_eq (hp2 : p ≠ 2) (a : ZMod p) : (pointCount p a : ℤ) = p + 1 + jac a
theorem jac_sq_mul {k : ZMod p} (hk : k ≠ 0) (a : ZMod p) :
    jac (k ^ 2 * a) = quadraticChar (ZMod p) k * jac a
theorem sum_quadraticChar_shift_mul {α β : ZMod p} (h : α ≠ β) :
    ∑ t : ZMod p, quadraticChar (ZMod p) ((t + α) * (t + β)) = -1
theorem jacobsthal (hp4 : p % 4 = 1) {r : ZMod p} (hr : ¬ IsSquare r) :
    jac (1 : ZMod p) ^ 2 + jac r ^ 2 = 4 * p
theorem four_dvd_pointCount (hp4 : p % 4 = 1) {D : ZMod p} (hD : D ≠ 0) :
    4 ∣ pointCount p (-D ^ 2)
-- File 2
def InClass (p : ℕ) : Prop := p % 8 = 1 ∧ (p % 7 = 3 ∨ p % 7 = 5 ∨ p % 7 = 6)
theorem gcd_pointCount_eq (hp : p.Prime) (hC : InClass p) {r : ZMod p} (hr : r ^ 2 = 2) :
    Nat.gcd (pointCount p (-(75 - 53 * r) ^ 2)) (pointCount p (-(75 + 53 * r) ^ 2))
      = 4 * Int.gcd (cp p) (p + 1)
theorem goodSlopePrime_of_gcd (hp : p.Prime) (hC : InClass p)
    (h : Int.gcd (cp p) (p + 1) = 1) : GoodSlopePrime p
theorem mod_four_of_dvd_cp {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hp : p.Prime) (hC : InClass p)
    (h1 : (ℓ : ℤ) ∣ cp p) (h2 : ℓ ∣ p + 1) : ℓ % 4 = 1
-- File 9
def BadSet (ℓ : ℕ) : Set ℕ := {p | p.Prime ∧ InClass p ∧ (ℓ : ℤ) ∣ cp p ∧ ℓ ∣ p + 1}
def UniformBadBound : Prop :=
  ∃ A N₁ : ℝ, 0 < A ∧ ∀ N : ℕ, N₁ ≤ N → ∀ ℓ : ℕ, ℓ.Prime → ℓ % 4 = 1 → 5 ≤ ℓ →
    ((ℓ : ℝ) ^ 4 ≤ N) →
    (((Finset.range (N + 1)).filter (· ∈ BadSet ℓ)).card : ℝ) ≤ A * N / (ℓ ^ 2 * Real.log N)
theorem goodPrimeDensity_of_uniformBadBound (h : UniformBadBound) :
    GTSearch.PrimesRelUpperDensityPos {p | GoodSlopePrime p}
theorem uniformBadBound : UniformBadBound          -- file 8
theorem goodPrimeDensity : GTSearch.PrimesRelUpperDensityPos {p | GoodSlopePrime p}
```

The final link is `progressions_above_of_greenTaoDense` (`scratch/gt-search/GreenTaoReduction.lean`)
applied to `goodPrimeDensity` with `S := Mult.S_b`. It gives
`GreenTaoDense → GoodPrimeAP` and hence the main theorem under the single hypothesis Green–Tao 1.2.

### 6.2 Order and milestones

1. **Milestone 1 (files 1, 2).** `goodSlopePrime_of_gcd`. Sanity checks against the existing
   `goodPatternPrime_seventeen`: `cp 17 = −1` (`p = 1 + 16`) and `cp 41 = −5` (`41 = 25 + 16`), by
   `decide` on `jac`; `scratch/pd-paper` gives the values for the class primes below 324.
2. **Milestone 2 (files 3, 4, 5, 6, 9 conditional).** `goodPrimeDensity_of_uniformBadBound`. This reduces
   Proposition D to one explicit, elementary counting statement about integers. It is already a
   better trust base than "Proposition D (sketch)": the hypothesis mentions neither density nor
   elliptic curves.
3. **Milestone 3 (file 7).** Port the PrimeNumberTheoremAnd sieve files. They need only Mathlib's
   `SelbergSieve.lean`, `ArithmeticFunction` and `Batteries`. They are Apache-2.0; keep the headers and
   add a notice.
4. **Milestone 4 (file 8).** `uniformBadBound`, hence `goodPrimeDensity` unconditionally.

### 6.3 The hardest steps

- **Lemma 4.3/4.4 in Lean (file 8).** Counting `(U, V) ∈ (ℤ/d)²` with `d | F(U, V)` for squarefree `d`,
  through `ZMod.prodEquivPi` and the factorisation of `x² + y²` over `ZMod q`. Then counting a box with
  residue conditions, uniformly. These are routine but long finite-combinatorics proofs. The
  `BoundingSieve` interface wants `support : Finset ℕ` with `weights` as multiplicities. Define
  `weights n = ((ℬ.filter (F · = n)).card : ℝ)`.
- **Claims A and B (file 8).** Alternating partial sums, the Euler–Mascheroni bracket, the convolution
  inequality `r ≤ h ∗ v` (a multiplicativity argument on prime powers), and `V ≤ 2ζ(2)⁴` (through
  `hasSum_zeta_two` and an `lcm` count). An alternative for Claim B: bound `Σ_{m≤w} v(m)/m` by an Euler
  product over primes `≤ w` (PrimeNumberTheoremAnd's `prod_factors_sum_pow_compMult` has this shape).
- **`selbergBoundingSum` versus `S₀`.** PrimeNumberTheoremAnd's `selbergBoundingSum_ge_sum_div` assumes
  `ν` completely multiplicative and every prime `≤ level` in `P`. Neither holds here, so Lemma 4.5 needs
  its own proof. The structure (`g(l) ≥ ∏_{q|l} 2/q` on `l | P`) is simpler than that lemma.
- **Analysis plumbing (files 3, 4).** `tsum` over `ℕ` with real exponents, summability, and the passage
  from `residueClass` (which includes prime powers) to sums over primes. Mathlib's
  `summable_residueClass_non_primes_div` and `LSeries_residueClass_lower_bound` do the analytic work.

### 6.4 Effort tiers

| Tier | Work | Result |
| --- | --- | --- |
| cheap win | files 1, 2 (about 500–750 lines) | the CM description, without CM theory; the earlier estimate for this piece (`gt-search.md` §4, D1) was 1.5–3k lines |
| medium investment | files 3, 4, 5, 6, 9-conditional (about 1–1.5k lines) | Proposition D modulo `UniformBadBound` |
| bigger investment | files 7, 8 (port of 1.5k lines plus about 1–1.5k new) | Proposition D unconditionally; `GoodPrimeAP` from Green–Tao 1.2 alone |

Total new code is about 2.5–4k lines, plus the 1.5k-line port, against 6–10k in `gt-search.md` §4.

### 6.5 The first step

**State and prove `jacobsthal`, `four_dvd_pointCount` and `goodSlopePrime_of_gcd` (files 1, 2).**
*Success criterion:* the three theorems build against the pinned Mathlib. `#print axioms
goodSlopePrime_of_gcd` reports `[propext, Classical.choice, Quot.sound]`. And
`goodSlopePrime_of_gcd` reproves `GoodSlopePrime 17` from `InClass 17` and `cp 17 = −1`.
Success proves that the step considered the most specialised (D1 of `gt-search.md`: point counts of a
CM curve through quartic Jacobi sums) is a few hundred lines of character sums. It also gives the
interface (`InClass`, `cp`, `BadSet`) on which every later file is stated.

---

## 7. Ranking of routes

| Rank | Route | Payoff | Main obstacle | Chance |
| --- | --- | --- | --- | --- |
| 1 | **DS-cond**: files 1–6 and 9, ending with `goodPrimeDensity_of_uniformBadBound` | Proposition D reduced to one explicit counting statement (`UniformBadBound`) | analysis plumbing (`tsum`, Abel summation, CRT counts) | high |
| 2 | **DS**: Route 1 plus the port of the PrimeNumberTheoremAnd sieve and the two-dimensional instance (file 8) | `GoodPrimeAP` follows from Green–Tao 1.2 alone; Proposition D proved | Lemmas 4.3–4.5 in Lean; porting 1.5k lines | high |
| 3 | **NAT**: natural density through `WeakPNT_AP` | positive lower natural density, matching `nt-22p.md`'s wording | importing PrimeNumberTheoremAnd (`v4.34` pins; two `sorry`s in `Wiener.lean` whose reach is unconfirmed) | medium |
| 4 | **H**: Hecke for `ℚ(i)` | the exact density `0.1060…` | Hecke `L`-functions and their non-vanishing on `Re s = 1`, none in Mathlib | low |
| 5 | **NS**: a subset of `G` that avoids the uniform sieve | would remove file 8 | §4.6: every candidate fails | low |

**Route 1 (DS-cond).**
- *Payoff.* The trust base for `GoodPrimeAP` becomes Green–Tao 1.2 plus `UniformBadBound`. The latter
  is a statement about integers `p ≤ N` with `p = c² + e²`, `ℓ | c`, `ℓ | p + 1`, checkable by anyone
  familiar with sieves, and it is the manuscript's own estimate (lines 1600–1624) in a simpler setting.
  The CM step is fully proved (Proposition 1.6).
- *Main obstacle.* Files 3 and 4: real-exponent `tsum`s and the CRT count of `A_L`. Both are routine.
- *First test.* §6.5. *Success criterion:* `goodSlopePrime_of_gcd` builds with standard axioms and
  reproves `GoodSlopePrime 17`.
- *Chance: high.* Every step is elementary, written out above, and tested numerically (§1–§2). The
  Mathlib statements used were read in the source.

**Route 2 (DS).**
- *Payoff.* Proposition D becomes a theorem. With a formal Green–Tao 1.2 (`gt-search.md` §1), the main
  theorem's AP variant would need no number-theoretic hypothesis beyond those already in the kernel.
- *Main obstacle.* File 8. Lemma 4.3 is easy on paper but needs a CRT count of a two-dimensional
  residue set. Lemma 4.5 needs Claims A and B. `selberg_bound_simple` exists and is sorry-free, but it is
  pinned to Lean `v4.34.0`. The module proxy had no `v4.35.0` archive.
- *First test.* Port `Sieve/Selberg.lean` and its three companions to the pinned Mathlib, and
  instantiate `BoundingSieve` for one fixed `ℓ` (say `ℓ = 5`) with the box `ℬ` of §4.3. *Success
  criterion:* `selberg_bound_simple` applies, `multSum_eq` is proved in the form of Lemma 4.4, and the
  port compiles without `sorry`.
- *Chance: high.* The mathematics is complete, with explicit constants. The risk is volume
  (1–1.5k new lines), not a missing idea.

**Route 3 (NAT).** *Payoff:* lower natural density instead of Dirichlet density; cosmetic for
`GoodPrimeAP`. *Obstacle:* a version mismatch, and the `sorry`s in `Wiener.lean`. *First test:*
`#print axioms WeakPNT_AP` in a PrimeNumberTheoremAnd build; success if it reports no `sorryAx`.
*Chance: medium*: it depends on someone else's project.

**Route 4 (H).** *Payoff:* the constant `(1/8)∏(1 − 2/(ℓ − 1)²)`; not used anywhere. *Obstacle:* ray
class characters of `ℚ(i)`, their `L`-functions, and `L(1, ψ) ≠ 0`. *First test:* none sensible before
Mathlib has Hecke characters. *Chance: low.*

**Route 5 (NS).** *Payoff:* would remove file 8. *Obstacle:* §4.6; the joint condition on `(c_p, p)` at
all large `ℓ` has no one-variable substitute. *First test:* find a set `G′ ⊆ G`, defined by conditions
on `p` modulo integers or by Chebotarev conditions in a fixed field, with positive density. Success if
`density.py` shows `G′ ⊆ G`. The independence heuristic predicts failure. *Chance: low.*

**Recommendation.** Do Route 1 now (it starts with the first step of §6.5), then Route 2. Route 1 alone
already replaces the unwritten Proposition D by a proved reduction to an explicit sieve estimate.

---

## 8. Open questions

1. Does PrimeNumberTheoremAnd have a tag for Lean 4.35 under another name? Only `v4.34.0` was found.
   If not, the port of file 7 is from `v4.34.0` (`c39a7511`).
2. Can a cheaper upper-bound sieve replace the optimal Selberg weights? For example, take
   `λ_d = μ(d)·max(0, log(w/d))/log w` and evaluate the main term directly. That would avoid
   `selberg_bound_weights`, but needs an asymptotic for `Σ_{d,e} λ_dλ_e ν([d, e])`, which is probably
   longer.
3. The lean-eval Green–Tao solutions (`gt-search.md` §1.1) prove Theorem 1.1. Whether their
   transference takes a dense subset (Theorem 1.2) is the other half of the trust base. It is outside
   this note.
4. Is `UniformBadBound` true with `A = 1` for all `N ≥ 10⁸`? The data suggest a constant near `0.3`.
   This does not matter for the proof.

## References

- Manuscript `diophantine_zq.tex`, lines 1291–1704 (proof of Proposition 6.2), in particular
  1554–1598 (conjugate orders) and 1600–1642 (bad prime values); records A021, A072.
- `docs/research/nt-22p.md` §2 (Proposition D sketch), `rv-nt22p-ap.md` F5 (branch `wip/rv-nt22p-ap`),
  `aud-ap.md` §1.3–1.4 (branch `wip/aud-ap`), `gt-search.md` §3–4 (branch `wip/gt-search`).
- B. Green, T. Tao, *The primes contain arbitrarily long arithmetic progressions*, Ann. of Math. 167
  (2008), Theorem 1.2 (statement VERIFIED in `rv-nt22p-ap.md` §5 from the arXiv TeX source).
- E. Jacobsthal, *Über die Darstellung der Primzahlen der Form 4n + 1 als Summe zweier Quadrate*, J. reine
  angew. Math. 132 (1907) (UNCHECKED; Lemma 1.4 is proved in full above).
- K. Ireland, M. Rosen, *A Classical Introduction to Modern Number Theory*, 2nd ed., Ch. 18 §4
  (UNCHECKED; not used).
- H. Halberstam, H.-E. Richert, *Sieve Methods* (1974), for the Selberg upper-bound sieve (STANDARD; the
  closed bound used is `SelbergSieve.selberg_bound_simple` of PrimeNumberTheoremAnd, read in source).
- Mathlib `56a005855ea1`: `NumberTheory/LSeries/PrimesInAP.lean`, `NumberTheory/NumberField/DedekindZeta.lean`,
  `NumberTheory/NumberField/DirichletDensity.lean`, `NumberTheory/SelbergSieve.lean`,
  `NumberTheory/Chebyshev.lean`, `NumberTheory/LegendreSymbol/*`, `NumberTheory/Harmonic/EulerMascheroni.lean`,
  `RingTheory/Frobenius.lean`, `Data/ZMod/QuotientRing.lean`.
- PrimeNumberTheoremAnd `v4.34.0` (`c39a751132c8`): `PrimeNumberTheoremAnd/Mathlib/NumberTheory/Sieve/*.lean`,
  `PrimeNumberTheoremAnd/BrunTitchmarsh.lean`, `PrimeNumberTheoremAnd/Wiener.lean`.
- Scripts: `scratch/pd-paper/lemmas.py` (checks A–E), `gcdformula.py` (check F), `density.py`
  (outputs `density_1e7.out`, `density_1e8.out`), `sieveaux.py` (output `sieveaux.out`).
