# The height hypothesis H: what is used, what a change of construction can and cannot buy, and an older modularity input

Status labels. **VERIFIED**: checked against the manuscript `diophantine_zq.tex` (line numbers
refer to the frozen 11/5 source), against the Lean development, or by a computation whose script
is in `scratch/nt-h/` (output beside it as `*.output.txt`). **STANDARD**: a published theorem
whose statement was checked to apply; the reference is given. **SPECULATIVE**: an idea or an
assessment, not proved. **UNCHECKED**: the source could not be read here; the attribution is
recorded but the exact statement or numbering was not checked.

Notation as in `docs/research/rs-height.md`. `𝒞 = {0,-15,-20,-24,-30,-60}`,
`F(u) = ∏_{c∈𝒞}(u-c)`, `h(a/b) = log max(|a|,b)`. `M_S(u)` is the product of the primes `p ∉ S`
at which some `v_p(u-c)`, `c ∈ 𝒞`, is positive and odd. `S_ht` = primes `≤ 324`,
`S_mul = S_ht ∪ 𝓗 ∪ supp(c_*)` (line 968, `ZInQ.Mult.S_mul`), `D` the degree constant with
`2^(2^8008) < D < 2^(2^9010)` (`ZInQ.Size.D_bounds`), `A0 = H₆(S_ht; D)`. For a twist class
`d = (d_c)_{c∈𝒞}`, `C_d` is the curve `d_c y_c² = a - cb` (`c ∈ 𝒞`) of genus 17
(rs-height §3.3). `A_u` is the QM abelian surface attached to `u` in the proof of Theorem 4.1, and
`r_ℓ` its two-dimensional representation of `G_ℚ` (line 730).

## Summary

- **What the consumers use (§1, VERIFIED).** The two consumers apply the estimate at a single
  adversarial rational number each: the slope `t` of an accepted multiplication certificate
  (`ZInQ.Mult.slope_height_le_of`) and the rational value `t` of an accepted main branch
  (`ZInQ.Assembly.ratHeight_le_bound_of_test`). They extract from `t` only `t ∉ 𝒞` and a
  divisibility of `M_S(t)` (or its 25th power) into an integer they control. The precision use
  tolerates any computable bound; the multiplication use tolerates any exponent `e < 25` with the
  present template (§1.3: the size chapter absorbs `e = 25 - 2^{-2^{65535}}`) and a constant `A` up
  to `log₂ A ≈ D^{2^{56000}}`, but not a super-polynomial shape.
- **No cheap restriction of `u` helps (§2).** Every restriction of the slopes that the
  construction can impose cheaply (images of rational maps, local conditions at finitely many
  primes, conic conditions) leaves a family of twists of a compact curve of genus `≥ 2`, or makes
  H false. A "rank-zero quotient" argument is vacuous: for all 131 points with `M_S = 1` for
  `S = {2,…,13}` found in rs-height §3.3, the image in each of the 15 elliptic quotients of the
  twist is non-torsion (VERIFIED, `quotients.py`). So every twist that has a point has all its
  elliptic quotients of positive rank.
- **Changes of construction (§3).** Three lemmas make the obstruction of rs-height R2/R4 and
  rs-global C1/C7 precise and general.
  - *Cusp lemma* (VERIFIED as an argument): at a cusp the reduction is multiplicative for every
    positive approach valuation, and every cusp is approached at infinitely many primes
    (Chebotarev). A test that sees valuations modulo `m` at all primes, or integrality at
    finitely many primes, never sees these primes. So no change of the precision or
    multiplication test of this kind makes a cusp available.
  - *Affine-moduli lemma* (VERIFIED as an argument): the parity mechanism forces the family to
    extend with potentially good reduction over the complete genus-17 curve `C`. Hence its moduli
    map lands in a moduli space containing complete curves. The moduli spaces in which effective
    Shafarevich theorems are proved by Baker's method or S-unit equations (elliptic curves,
    `M_{0,n}`, hyperelliptic curves, genus two) are affine, so they only receive isotrivial
    families. What is left is abelian varieties (`A_g`, `g ≥ 2`) or curves of genus `≥ 3`. There
    the only known effective Shafarevich bounds go through modularity.
  - *Detection lemma* (VERIFIED as an argument): detecting all positive valuations is rs-global
    C1 even in the multiplication test, where true triples have `f = 0`. The reason is that
    completeness of the pole predicate brings back the full set of PC inputs.
  - Conclusion: within architectures whose local tests are parity or valuation-mod-`m` tests,
    QM surfaces over the disc-6 Shimura curve over `ℚ` are the cheapest family that can work
    (SPECULATIVE in this generality, argued in §3.6). Removing H by a change of construction would
    need a new kind of local test, and C1 says that kind is the theorem itself.
- **An older modularity input (§4).** The modularity step can use Serre's 1987 argument at
  varying `ℓ`: Khare–Wintenberger's theorem (Serre's conjecture in its strong form, with level
  `N(r̄_ℓ)` and weight 2) at infinitely many large `ℓ` outside `T`, then a pigeonhole over the
  finitely many weight-2 newforms of level `≤ QM²`. This replaces Pan's theorem at `ℓ = 5`
  (A011). It also removes the p-adic Hodge theory (A009 with the appendix lemma, A010 Berger,
  Conrad's local algebraicity) and Carayol's local–global compatibility, because the level comes
  out of the strong form. Faltings' `ℓ`-adic theorems at `ℓ = 3, 5` (A008) give way to the
  large-`ℓ` mod-`ℓ` theorem, where Masser–Wüstholz's effective version applies. The argument is
  written out in §4.1 (VERIFIED as an argument). The exact numbering in Khare–Wintenberger and in
  the level- and weight-optimization papers is UNCHECKED. The depth is unchanged (modularity
  lifting underlies both theorems), but every modularity input is from 2009 or earlier.
  Constants are unchanged.
- **Ranking (§5).** (1) Swap to Serre's argument at large `ℓ`: medium payoff, high chance.
  (2) Restate the consumers' hypotheses in their "consumer shape": small payoff, high chance.
  (3) A new kind of local test that sees positive valuations at all primes without defining
  `ℤ`: would remove H; chance nil by C1. (4) Effective Shafarevich for QM surfaces without
  modularity: would remove modularity from H; very low chance.

## 1. The statement and its two consumers

### 1.1 The hypothesis (VERIFIED)

`ZInQ.SixContactMin` (`ZInQKernel/Hypotheses/HeightMin.lean`, line 36):

> for every `u ∈ ℚ \ 𝒞`, `ratHeight u ≤ heightH6 heightD · contactSupport S_mul u ^ 24`,

the instance `S = S_mul`, `R = D` of manuscript Theorem 4.1 (`thm:height`, lines 404-408).
`sixContactMin_of_sixContactEstimate` (`Main.lean`, line 56) derives it from the manuscript's form.

### 1.2 The consumers (VERIFIED by reading the Lean proofs)

**Use P.** `Assembly.ratHeight_le_bound_of_test` (`Assembly/Top/MainBranch.lean`, line 27) takes
`n ∉ 𝒞` and `Test n κ t`, extracts `t ∉ 𝒞` and `M_{S_ht}(t) ∣ κF(n)` (`test_dvd`, manuscript
Lemma 11.1, lines 6151-6200) and applies `sixContact_at_heightPrimes` (`HeightMin.lean`, line 76)
at `u = t`. The conclusion is `h(t) ≤ 𝓑(n,κ) = A0|κF(n)|^{24}`. Then `eq_of_close_of_test`
(line 42) combines it with `|t - n| < e^{-𝓑}` to get `t = n`. The Liouville step
`eq_int_of_real_abs_sub_lt_exp_neg_of_height_le` uses only `log den(t) ≤ h(t) ≤ 𝓑`.

**Use M.** `Mult.slope_height_le_of` (`Multiplication/Soundness/ContactSupport.lean`, line 49)
takes the estimate as a hypothesis `hest : ∀ u ∉ 𝒞, h(u) ≤ A·M_S(u)^{24}` but applies it only at
the slope `t` of `SlopePred t ℓ (c₀, c₀n₀, c₀n₁, c₀n₂)`, with `f = n₀n₁ - n₂ ≠ 0`. It derives
`M_S(t)^{25} ∣ f` from the local congruences (`local_congruence_of`). The conclusion is
`h(t) ≤ A|f|^{24/25}`. `slope_height_le` instantiates `S = S_mul`, `A = A_ht` through
`sixContact_at_Smul` (`ConstantsProperties.lean`, line 135).

So the formal content each consumer needs is the "consumer-shaped" statement

- **H_P^c.** For all `n ∉ 𝒞`, `κ ≠ 0` and `t` with `Test n κ t`: `h(t) ≤ A0|κF(n)|^{24}`.
- **H_M^c.** For all `n` with `f ≠ 0` and `t` with `SlopePred t ℓ₀ (certShifts n)`:
  `h(t) ≤ A_ht|f|^{24/25}`.

Both follow from H_min. Both are formally weaker, since `Test` and `SlopePred` also contain the
pole predicate `Φ` and the formal-group witnesses. §2.4 explains why that extra content cannot be
exploited.

### 1.3 The slack, quantified (VERIFIED: `slack.py`, from the bounds of rs-height §2.3)

- **Use P: shape free, effectivity essential.** Any monotone bound `Φ(M_{S_ht}(t))`, or more
  generally `Φ(κF(n))`, that the precision machine can compute works (rs-height §2.2). The bound
  may even depend on the archimedean size of `t`: since `|t - n| < 1`, the factor `|F(n)|^{24}`
  in `𝓑` already allows `h(t) ≤ A0(M(t)·max(1,|t|)^6·2^6)^{24}`. This buys nothing, because the
  difficulty is the denominator of `t`, which none of the tests sees (rs-height §3.3).
- **Use M: exponent.** With the present template (test valuation `k = 25`), a bound
  `h(t) ≤ A·M^e` gives `N < (48A)^m` with `m = 25/(2(25-e))` (rs-height §2.3). The target needs
  `log₂log₂(T+1) < 2^{65536} - 11` (`triplePower_9014_lt_tower_seven`). With
  `log₂ A < D^7`, any `m` with `log₂ m < 2^{65536} - 7·2^{9010} - 13` is admissible. So every
  exponent `e ≤ 25 - 2^{-2^{65535}}` is absorbed by redefining `T = (48A)^{⌈m⌉+1}` and
  re-proving the size lemma for that `T`. The test valuation and the multiplication template stay
  as they are. Exponents `e ≥ 25` need a larger `k` (a longer truncated logarithm `L` and new
  valuation margins at lines 1150-1157).
- **Use M: constant.** At `e = 24`, `log₂ A = D^x` is admissible for every `x < 2^{56525}`. The
  current value is `x = 7`.
- **Use M: shape.** A super-polynomial bound in `M` cannot be absorbed by any fixed `k`
  (rs-height §2.3, §2.4). The dependence on `M` is forced: with `M = 1` the bound would cap the
  heights of all accepted slopes, including those that completeness needs for true triples.

So the target tolerates almost any explicit polynomial bound. What it cannot do without is the
uniformity in the twist: one explicit polynomial must work for all of the infinitely many curves
`C_d`.

## 2. Weaker statements: thin sets, averages, consumer shapes

### 2.1 The quantifier over u (VERIFIED as a reading of the Lean statements)

In both uses `t` is an existential witness chosen by whoever satisfies the formula, so soundness
is a worst-case statement. The divisibility hypotheses can be met for every `t ∉ 𝒞`: take `κ` or
`f` divisible by `M(t)^{25}` (rs-height §1.4). An averaged bound, or a bound outside an
exceptional set of density zero, is useless: one exceptional `t` with an accepting set of
witnesses breaks soundness.

### 2.2 Restrictions the construction could impose cheaply

A restriction of the slopes is usable only if (i) it is expressible by a few extra polynomial
equations with rational witnesses, and (ii) completeness survives: for true triples the nine
coordinate quantities must still be sums of three admissible slopes satisfying the prime pattern
22P. The cheap restrictions are of three kinds. None helps (VERIFIED as arguments):

- **Images of rational maps**, `t = φ(s)` with `φ ∈ ℚ(s)` of degree `≥ 2`. H restricted to
  `φ(ℚ)` asks for rational points on the pull-backs `C_d ×_{ℙ¹_u} ℙ¹_s`, again twists of one
  compact curve. Its genus is at least 17 unless `φ` factors through part of the conic tower. For
  example, `t = c₀ + s²` leaves a `(ℤ/2)⁴`-cover of `ℙ¹_s` branched at 10 points, of genus 25. If
  `φ` absorbs enough of the tower to bring the genus down to `≤ 1`, the twists acquire positive
  rank and heights become unbounded at fixed `M`, so H is false on `φ(ℚ)` (rs-height R7).
- **Local conditions at finitely many primes** (congruences, integrality at a fixed `p`). These
  cut out an open subset of `∏_{p∈P} ℙ¹(ℚ_p)`. The twists `C_d` and their rational points outside
  `P` do not change.
- **Conic conditions** such as `t - c₀ ∈ ℚ^{×2}`. These are the case `d_{c₀} = 1` of the twist
  family, which is the image-of-a-map case.

### 2.3 Rank-zero quotients are vacuous on the twists that matter (VERIFIED)

`Jac C_d` is isogenous to 15 elliptic curves `E_I^{(d)}` (`|I| = 4`) and a CM surface
(rs-height §3.3). If some `E_I^{(d)}` had rank zero, which a 2-descent could certify, the points
of `C_d` would map to torsion and their heights would be bounded absolutely. But H concerns the
twists that have points. `quotients.py` takes the 131 points `u = a/b` with `M_S(u) = 1`,
`S = {2,3,5,7,11,13}`, `|a|, b ≤ 1500`. For each point it maps `u` to all 15 quotients
`Y² = D_I ∏_{c∈I}(u-c)`, `D_I = core(∏_{c∈I}(a-cb))`, through an explicit Weierstrass model,
and asks PARI for the order of the image. **In all 131 × 15 cases the image has infinite order.**
So every twist in this sample that carries a non-trivial point has all 15 elliptic quotients of
positive rank. A rank-zero argument bounds only twists with no points. The genus-2 factor
`y² = d·F(u)` has CM Jacobian over `ℚ̄`, but its twists carry the same points, so the same
remark applies.

### 2.4 The consumer-shaped statements (SPECULATIVE assessment)

H_P^c and H_M^c (§1.2) also assume that the pole predicate `Φ(R/Θ²)` is soluble for some choice
of the remaining witnesses. Solubility is a global condition (rational points on `E_e` and
`E_{eH}`). It would restrict `t` only if, for tall slopes, every choice of the free witnesses
`q, ℓ₀, H, U_i, e, z` led to an insoluble pole instance. Insolubility can be certified by
descent, but the witnesses form a positive-dimensional family, and `e` alone moves the instance
through a one-parameter family of curves. No mechanism is known that would make all of them
insoluble. Stating H_P^c and H_M^c in Lean is a refactor that shrinks the trust boundary
slightly, as R1 of rs-height did. It is not a route to a proof.
