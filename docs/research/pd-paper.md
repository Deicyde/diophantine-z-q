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
   density is Proposition 5.1. It needs only Abel summation and Chebyshev's bound `π(N) ≪ N/log N`.
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
   and no choice of `G*` avoids it (§4.6). PrimeNumberTheoremAnd's `SelbergSieve.selberg_bound_simple`
   (sorry-free, built on Mathlib's `BoundingSieve`) is the closed Selberg bound this needs.
5. **Lean plan** (§6). Nine files, about 3.5–5.5k lines. That is less than earlier estimates, because the
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

> **Theorem D.** There are `L` and `η > 0` such that `(x − 1)·Φ_{G*_L}(x) ≥ η` for all `x ∈ (1, x₀]`,
> for some `x₀ > 1`. In particular `liminf_{x→1⁺}(x − 1)Φ_G(x) > 0`.

through Proposition 5.1 (Dirichlet density ⇒ upper natural density). Theorem D gives a lower
Dirichlet density in the von Mangoldt normalisation. The classical normalisation
`Σ_{p∈G} p^{−x}/log(1/(x − 1))` is equivalent for this purpose (Remark 5.2). The full Proposition D of
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

