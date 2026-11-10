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

- **What the consumers use (§1, VERIFIED).** Each consumer applies the estimate at one
  adversarial rational number: the slope `t` of an accepted multiplication certificate
  (`ZInQ.Mult.slope_height_le_of`) and the value `t` of an accepted main branch
  (`ZInQ.Assembly.ratHeight_le_bound_of_test`). From `t` they use only `t ∉ 𝒞` and the fact that
  `M_S(t)` (or its 25th power) divides an integer they control. The precision use tolerates any
  computable bound. With the present template, the multiplication use tolerates any exponent
  `e ≤ 25 - 2^{-2^{65535}}` and any constant with `log₂ A = D^x`, `x < 2^{56525}` (now `x = 7`),
  but no super-polynomial shape. What cannot be weakened is uniformity over the infinitely many
  twists `C_d`.
- **No cheap restriction of `u` helps (§2).** Soundness is a worst-case statement about one
  existential witness, so bounds on average or outside a thin set are useless. Every restriction
  the construction can impose cheaply leaves twists of a compact curve of genus `≥ 2` or makes H
  false. A rank-zero-quotient argument is vacuous. For all 131 points with `M_S = 1`,
  `S = {2,…,13}`, the image in each of the 15 elliptic quotients of the twist has infinite order
  (VERIFIED, `quotients.py`).
- **Changes of construction (§3).**
  - *Cusp lemma* (VERIFIED as an argument). Each cusp of a family over `ℙ¹_u` is approached at a
    set of primes of positive density. At those primes the fibre is bad for every positive
    valuation, even or odd, so parity tests never see them. Adding integrality tests at finitely
    many primes is cheap but does not help.
  - *An instance* (VERIFIED, `genus2cusp.py`). As genus-two *curves*, the fibres of the present
    family degenerate at every prime with a positive contact valuation: `J₁₀ = j³` vanishes
    exactly at the contacts, and `J₂⁵/J₁₀` is non-integral in all 19 cases tested. So the
    Baker-accessible effective Shafarevich theorems for genus-two curves would need all those
    primes in the conductor. Only the Jacobians are cusp-free.
  - *Affine-moduli lemma* (VERIFIED as an argument). A family with the parity-to-good-reduction
    property has no cusps, so its moduli map sends `ℙ¹_u` to a complete curve. The moduli spaces
    where Baker or `S`-unit methods give effective Shafarevich theorems (elliptic curves, genus
    two, hyperelliptic, cyclic covers) are affine, so they carry only isotrivial families, which
    lose the height (rs-global C7). What remains is complete curves in `A_g` or `M_g`. There the
    only known polynomial height bound is for `GL₂`-type fibres through modularity, so QM
    surfaces are the cheapest choice (SPECULATIVE as a claim about the literature).
  - *Relative positivity* (§3.5). C1 does not exclude a test enforcing "`v_p(t - c) > 0 ⇒ p ∣ K`"
    relative to the controlled label integer `K`, since true inputs never need `K = ±1`. Such a
    test would replace H by the Stewart–Yu `S`-unit bound, a Baker-type result. But no
    existential local device sees positive valuations at all primes, so this route has no known
    first step.
- **An older modularity input (§4).** Serre's 1987 argument at varying `ℓ` applies: Khare–
  Wintenberger's strong form of Serre's conjecture at infinitely many large `ℓ ∉ T` (level
  `N(r̄_λ) ≤ QM²`, weight 2 by finite flatness), then a pigeonhole over the finitely many
  weight-2 newforms of level `≤ QM²`. This replaces Pan's theorem (A011). It removes the de Rham
  comparison (A009), Berger (A010) and Conrad's local algebraicity. Carayol's compatibility stops
  being a separate leaf but stays inside the citation of the strong form. Faltings at `ℓ = 3, 5`
  is replaced by the mod-`ℓ` theorem for almost all `ℓ`, and no effective `ℓ` is needed. The
  argument is written out in §4.2 (VERIFIED as an argument; the theorem numbers are UNCHECKED).
  Depth is unchanged, constants are unchanged, and the modularity input dates from 2009.
  Langlands–Tunnell with 3-adic lifting, level lowering alone, and modular parametrizations of
  `X⁶/W` do not apply (§4.4).
- **Ranking (§5).** (1) Serre's argument at large `ℓ`: medium payoff, high chance. (2) Combine it
  with h-leaves: small extra, high chance. (3) Consumer-shaped hypotheses in Lean: small payoff,
  high chance. (4) A relative positivity test: would remove H, very low chance. (5) Effective
  Shafarevich for QM surfaces without modularity: very low chance. (6, 7) Thin sets, rank-zero
  quotients, elliptic or genus-two families: settled negatively.

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

## 3. Changes of construction: cusps, moduli and the local tests

The question is whether some change of the contact set, the family or the tests turns H into a
statement about integral points, `S`-unit equations or a family with elementary height control,
as Route K turned pole completeness into rank one for congruent number curves. Route K worked
because the new statement was *true for a structural reason with a published proof behind it*
(Tian–Yuan–Zhang) and the rest was a descent. For H, the corresponding published theorems are
effective Shafarevich theorems, and §§3.1-3.5 locate exactly which of them the architecture can
reach.

### 3.1 What the mechanism needs (VERIFIED, lines 510-563)

The proof of Theorem 4.1 attaches to `u ∈ ℚ \ 𝒞` an abelian surface `A_u` over a field `K` of
degree `≤ 324` that is unramified outside `T = S ∪ supp M_S(u)`, with good reduction outside `S`.
Lines 510-534 give the local form: near a contact, `u - c = z²` up to a unit, so an *even*
valuation `v_p(u - c)` gives an unramified local extension, and the level-3 structure gives good
reduction there. Two properties of the family are used:

- (G) at every prime `p ∉ S` and every `u` with all contact valuations even at `p`, the fibre
  has good reduction over an unramified extension of `ℚ_p`;
- (H) the size of the fibre (its Faltings height) is bounded polynomially in its conductor.

(G) is what links the local tests, which see `v_p(u - c) mod 2`, to arithmetic. (H) is the deep
input. Any replacement of the family must keep (G) and make (H) cheaper.

### 3.2 The cusp lemma (VERIFIED as an argument; ingredients STANDARD)

Call a closed point `α` of `ℙ¹_u` a *cusp* of a family of abelian varieties (or of curves) over
an open set of `ℙ¹_u` if the family does not have potentially good reduction at `α`, i.e. its
moduli map sends `α` to the boundary of a toroidal or stable compactification.

**Lemma C.** Let `α` be a cusp of degree `k` over `ℚ`. Then:

1. the set `P_α` of primes `p` at which `α` has a `ℚ_p`-rational point has Dirichlet density at
   least `1/k` (Chebotarev applied to the Galois closure of `ℚ(α)`; STANDARD);
2. for all `p ∈ P_α` outside a finite set and every `u ∈ ℚ` with `m = v_p(u - α) > 0` (computed
   in `ℚ_p` at a `ℚ_p`-point of `α`), the fibre at `u` has bad reduction at `p`, and stays bad
   after every finite extension of `ℚ_p`. For a family of abelian varieties the Tate parameter of
   the toric part has valuation `m · w > 0` (`w` the width), so the toric rank is positive for
   every `m ≥ 1`. For a family of curves the stable reduction is singular.

So at the primes of `P_α` the bad reduction comes from `v_p(u - α) > 0` whatever its parity.
Suppose a soundness proof argues by local insolubility, as every soundness argument of the
manuscript does (Lemma 5.1 at lines 987-1000; the test lemma at lines 6151-6200). Then at a
prime `p ∈ P_α` where all contact valuations of `u` are `0`, the local solubility of every
parity test is the same for `v_p(u - α) = 0` and for `v_p(u - α) = 2`, since it depends only on
the contact valuations modulo 2. So such a proof cannot conclude that `p` divides the controlled
integer (`κF(n)` in use P, `f` in use M). The conductor of the fibre then contains primes the
test does not bound, and (H) yields nothing.

Placing `α` among the contacts does not help either. Odd valuations become visible, but an even
positive valuation at `α` still gives bad reduction (item 2), and parity tests do not see it.
This is rs-height R4, now with the quantifier made explicit: the trouble is not one cusp but the
positive-density set `P_α` of approach primes.

### 3.3 An instance inside the present construction: the genus-two curve (VERIFIED)

The QM surfaces `A_u` are Jacobians of genus-two curves away from the decomposable locus. Their
Igusa invariants (line 538, from Lin–Yang (2), (14)) are
`[J₂, J₄, J₆, J₁₀] = [12(j+1), 6(j²+j+1), 4(j³-2j²+1), j³]`, `j = J(u) = -57600F(u)²/G(u)⁶`.
So `J₁₀ = j³` vanishes exactly at `j = 0`, i.e. at the six contacts (`F(u) = 0`). The contact set
is precisely the preimage of the decomposable locus. By Liu's criterion (Q. Liu, Math. Ann. 295
(1993); STANDARD, theorem number UNCHECKED), a genus-two curve has potentially good reduction at
`p` only if `J₂⁵/J₁₀ = 12⁵(j+1)⁵/j³` is `p`-integral. `genus2cusp.py` evaluates `v_p(J₂⁵/J₁₀)` for
19 inputs at primes `331 ≤ p ≤ 353`: contact valuation `1` at `c = -15`, contact valuation `2` at
`c = -15` and `c = -24`, and `u` `p`-adically close to a root of `G` (for `p ≡ 1 mod 3`). In every
case the valuation is negative (`-6`, `-12`, `-12`, `-24`). So **the genus-two curve `C_{J(u)}`
has bad stable reduction at every prime with a positive contact valuation, even or odd, and at
the approach primes of the roots of `G`**, while its Jacobian has good reduction there (lines
545-563). As curves, the six contacts and the two roots of `G` are cusps of the family; as
abelian surfaces, the family has none.

This matters for Baker-type routes. Effective Shafarevich theorems for genus-two and hyperelliptic
curves are proved by Baker's method through discriminant and `S`-unit equations (Smart, Math.
Comp. 66 (1997); von Känel, J. Théor. Nombres Bordeaux 26 (2014); STANDARD as references, not
re-read here). They bound curves with good reduction outside a set `S'`. For `C_{J(u)}`, the set
`S'` must contain every prime with a positive contact valuation, which is the full support of
`F(u)`'s numerator. So the curve route needs positivity detection at all primes, which is C1
(§3.4). The Jacobian route avoids the cusps, and that is why it needs modularity.

### 3.4 Tests that also see integrality (VERIFIED as arguments)

Could a precision or multiplication test that also detects integrality at some primes make a
cusp available? There are three cases.

- **Integrality at a fixed finite set `P`.** This is cheap: `ℤ_(p)` is Diophantine in `ℚ`
  (Koenigsmann 2016, Proposition 6, STANDARD and already used by the 10/11 manuscript at `p = 3`).
  Adding it to the tests would cost a few variables and a degree increase, with no change to
  Lemma 5.1 or to the size chapter beyond the variable budget (rs-global §2.4). But `P_α` is
  infinite (Lemma C(1)), so finitely many primes never cover the approach primes of a cusp.
- **Positivity at all primes, rational cusp.** Let `R(t, K)` say that `v_p(t - α) ≤ 0` for every
  prime `p ∤ K` outside a fixed finite `S₀`. If `R` were Diophantine, then
  `{1/(t - α) : R(t, 1)} = ℤ[1/S₀]` minus finitely many points would be Diophantine, and C1
  (`ℤ = Ψ ∩ ⋂_{p∈S₀} ℤ_(p)`) gives the main theorem. So the test is as hard as the target.
- **Positivity at all primes, irrational cusp** (`α` of degree `k ≥ 2`). Here `R(t, 1)` says that
  the numerator of the norm form `g(t) = N(t - α)` is an `S₀`-unit. For `k ≥ 3` this set is finite
  (Thue–Mahler), for `k = 2` it is a Pell-type set, so C1 does not apply directly. But no device
  of the manuscript's kind can express `R`. Parity devices see `v_p mod 2` (rs-global C2), and
  quadratic-form tests (Hasse–Minkowski, quaternion norms) see `v_p mod 2` at each prime. The
  known way to see positivity at a prime `p` uses `p` as a parameter of the test (Koenigsmann,
  Park), and quantifying over all `p` is a universal quantifier. That is exactly why those
  definitions of `ℤ` are `∀∃` rather than existential (rs-global A5). So this case would need a
  new kind of existential local test, and none is known (SPECULATIVE assessment).

So no change of the precision or multiplication test of the kinds considered makes a cusp
available, and the cost of trying would fall on the soundness lemmas (5.1 and the test lemma),
which would have to prove positivity rather than parity.

### 3.5 Relative positivity: what C1 does and does not exclude

C1 excludes a positivity predicate that is complete on a set containing `ℤ`. The consumers need
less. In use P the controlled integer is `K = κF(n)` with `κ, n` label integers (multiples of
`P₀`, `Assembly.Test`, `SixLocalTests.lean`, line 66), and in use M it is `f = n₀n₁ - n₂`.
Consider the *relative* condition

> (Pos_K) for every prime `p ∉ S₀` and every contact `c`: `v_p(t - c) > 0 ⇒ p ∣ K`.

True inputs satisfy it: for `t = n`, `v_p(n - c) > 0` gives `p ∣ F(n) ∣ K`. In use M, true triples
have `f = 0`, so (Pos_f) is vacuous for them. So completeness never asks for `K = ±1`, and the
argument of §3.4 (set `K = 1`) does not apply. VERIFIED as a reading of the two consumers.

If a test enforced (Pos_K), H would be unnecessary. Write `t = a/b`. Then `a - c_ib` is supported
on `S₀ ∪ supp K` for three contacts, and
`(c₂-c₃)(a-c₁b) + (c₃-c₁)(a-c₂b) + (c₁-c₂)(a-c₃b) = 0` is an `S`-unit equation. Stewart–Yu
(Duke Math. J. 108 (2001), STANDARD as cited in rs-height R2) bound it effectively, with
exponent `1/3 + ε` in the radical, giving `h(t) ≪ rad(K)^{1/3+ε}` up to `S₀`-factors. That is far
inside the slack of both uses (§1.3), and it rests on linear forms in logarithms only. Since
`S`-unit solutions have no uniformity problem in a twist, this would remove modularity, the
Shimura curve and all 23 leaves of h-leaves §5.1.

Why no such test is known (SPECULATIVE assessment, with VERIFIED ingredients):

- The label curve does supply relative information. `w([K]P₀)` has positive valuation at a good
  prime `p` exactly when `[K]P₀` reduces to `O`, so the formal group already turns "`p ∣ K`" into
  a local condition (this is how `test_dvd` works). The missing half is a local device that turns
  "`v_p(t - c) > 0`" into a local obstruction at every prime at once.
- The parity device cannot do this: its witnesses rescale by squares (the `q` in
  `a₀ = 1 - R₀q²`, and square scaling in Lemma 5.1), which neutralizes every even valuation
  (rs-global C2). Iterated square roots of depth `L` see valuations not divisible by `2^L`
  (rs-height R2). A finite depth always leaves `v_p = 2^L`.
- Quadratic forms and quaternion norms see positivity only at primes that are parameters of the
  form (rs-global A5). Making the parameter range over all primes needs a universal quantifier.
- An existential test that enforced (Pos_K) for all `K` in a set containing two coprime values,
  and accepted every `t` with `num(t - c) ∣ K^∞` (not only true inputs), would define
  `ℤ[1/K₁] ∩ ℤ[1/K₂] = ℤ` directly. So a usable device must be complete only on the special
  pairs `(n, κF(n))`. It would itself be a new Diophantine construction, of the same kind as the
  main theorem.

So the route stays open in logic but has no known first step. It is rs-height R2 with the
reason for "very low" stated precisely: no existential local device sees positive valuations at
all primes, even relative to a controlled integer.

### 3.6 The affine-moduli lemma (VERIFIED as an argument; ingredients STANDARD)

**Lemma M.** Let a family of abelian varieties (or of curves of genus `≥ 2`) over an open subset
of `ℙ¹_u` satisfy (G) of §3.1 for some finite contact set and all primes outside a finite set.
Then the family has no cusp. Its moduli map extends to a morphism from the complete curve `ℙ¹_u`
to the coarse moduli space (`A_g` or `M_g`), so its image is a complete curve or a point. If the
coarse moduli space of the family is affine, the family is isotrivial.

*Proof.* Let `α` be a cusp. By Lemma C(1) there are infinitely many `p ∈ P_α`. For such `p`
outside the finite exceptional sets, choose `u ∈ ℚ` with `v_p(u - α) = 2` and all contact
valuations at `p` zero. This is possible by weak approximation if `α` is not a contact, and
with `v_p(u - c) = 2` if `α = c` is a contact. All contact valuations are then even, so (G)
gives good reduction over an unramified extension. Lemma C(2) gives bad reduction after every
finite extension. Contradiction. With no cusp, the family has potentially good reduction at every
point of `ℙ¹_u`, so the moduli map extends over every point (Néron–Ogg–Shafarevich and the
stable reduction theorem; STANDARD). A morphism from a complete connected curve to an affine
variety is constant (STANDARD). ∎

The coarse moduli spaces that are affine include `M_{1,1} = 𝔸¹_j` and its level covers, the
configuration spaces `M_{0,n}` and their quotients, the hyperelliptic loci `H_g` (quotients of
`M_{0,2g+2}`), `M_2` (Igusa), and moduli of cyclic covers of `ℙ¹` (finite over quotients of
`M_{0,n}`) (STANDARD). These are exactly the families for which effective Shafarevich theorems
are proved by Baker's method or `S`-unit equations: elliptic curves over `ℚ` (Coates 1970),
genus-two curves (Smart 1997), hyperelliptic curves (von Känel 2014). The reason is the same in
each case: the branch points satisfy `S`-unit equations, and branch points live in `M_{0,n}`. The
claim "exactly" is an assessment of the literature known to us (SPECULATIVE). By Lemma M and C7
(isotrivial families lose the height), none of these families can carry H.

What remains is complete curves in `A_g` (`g ≥ 2`) or in `M_g` (`g ≥ 3`). The rational complete
curves in `A_2` include the Shimura curves of indefinite rational quaternion algebras, of which
`X⁶/W` is the simplest (rs-global C6). For a family over such a curve, (H) is an effective
Shafarevich theorem, and the only polynomial one we know is for abelian varieties of `GL₂`-type
over `ℚ`, through modularity (von Känel's method, used by the manuscript at lines 717-905). QM
surfaces are `GL₂`-type after the descent of lines 631-716. Families over complete curves whose
fibres are not of `GL₂`-type, such as Mumford's families in `A_4` or Kodaira fibrations in
`M_g`, have no known effective Shafarevich theorem at all. So among families satisfying (G), QM
surfaces over a rational quaternionic Shimura curve are the cheapest for (H) (SPECULATIVE as a
claim about the literature; the reduction to complete curves is VERIFIED as an argument).
Changing the discriminant `6` to another indefinite discriminant changes the contact set, not
the depth.

### 3.7 What §3 shows

- A family carrying the parity mechanism (G) has no cusps (Lemma M). So its moduli lie on a
  complete curve, and the Baker-accessible moduli spaces are excluded. The genus-two model of the
  present family shows this concretely: as curves, the fibres degenerate at every positive
  contact valuation (§3.3).
- Tests that add integrality at finitely many primes are cheap but useless, since the approach
  primes of a cusp form a set of positive density (§3.4).
- The only route that would make H Baker-accessible is a test enforcing relative positivity
  (Pos_K). It is not excluded by C1 (§3.5), and it would replace H by Stewart–Yu. But it needs an
  existential local device of a kind that does not exist in the literature.

So a Route-K-style change for H, unlike for pole completeness, has no candidate. For PC the change
kept the local tests and replaced the family of curves by one with a structural theorem behind it
(rank one through Heegner points). For H, the local tests fix the family up to the choice of a
rational quaternionic Shimura curve, and the structural theorem behind it is modularity.

## 4. An older modularity input: Serre's argument at large ℓ

### 4.1 The present step (VERIFIED, lines 717-857)

The manuscript builds `ρ_ℓ = r_ℓ ⊕ r_ℓ` on `G_ℚ`, with `r_ℓ|_{G_{L'}}` absolutely irreducible
(Faltings at `ℓ = 3, 5`, A008), de Rham with Hodge–Tate weights `0, -1` (appendix lemma, A009),
potentially semistable (Berger, A010), odd, and unramified outside `T ∪ {ℓ}`. Pan's Theorem 1.0.4
at `ℓ = 5` (A011) makes `r₅` modular up to a twist. Conrad's local algebraicity removes the twist
and forces weight 2. Li and Shimura give `r₅ ⊂ V(A_f)`. Traces then identify `r₃` with the
modular system, and Carayol's local–global compatibility (I1 of h-leaves) bounds the level of `f`
by the conductor of `r_ℓ`, which the local analysis bounds by `QM²` (lines 796-857). These local
bounds hold for every coefficient prime `ℓ ≠ p` (the argument at lines 814-846 uses only that
wild inertia above `U₀` acts trivially on `V_ℓ(A)` for `ℓ ≠ p`).

### 4.2 The replacement (VERIFIED as an argument; cited statements STANDARD, numbering UNCHECKED)

Fix the non-CM fibre `A = A_u` with the descended system `(r_λ)` of lines 717-796. Its traces
`t_p = tr r_λ(Frob_p)` lie in one number field `C` and are independent of `λ` (lines 776-790).
This independence comes from Frobenius endomorphisms of reductions of `A`, not from the modular
form.

1. **Residual irreducibility for almost all `ℓ`.** For all but finitely many `ℓ`, `A[ℓ]` is a
   semisimple `G_{L'}`-module and `End_{G_{L'}}(A[ℓ]) = O/ℓO`. This is the mod-`ℓ` form of
   Faltings' theorems (Faltings 1983; Zarhin; effective in Masser–Wüstholz, *Refinements of the
   Tate conjecture for abelian varieties*, 1995, cited by Zywina, Theorem 2.4, as recorded in
   h-leaves §4.5). Since `O/ℓ ≅ M₂(𝔽_ℓ)` for `ℓ ∤ 6`, the commutant of `r̄_λ|_{G_{L'}}` is the
   scalars, so `r̄_λ` is absolutely irreducible. No bound on the exceptional `ℓ` is needed below.
2. **Oddness** is inherited from `r_λ` (lines 742-752).
3. **Weight.** For `ℓ ∉ T`, `ℓ > 2`, `L` is unramified at `ℓ` and `A` has good reduction there,
   so `A[ℓ]` extends to a finite flat group scheme over the unramified ring `O_{L_v}`. By
   Raynaud's uniqueness of finite flat models for `e = 1 < ℓ - 1` (Raynaud, Bull. SMF 102
   (1974), §3.3, UNCHECKED numbering), the `G_{ℚ_ℓ}`-module `r̄_λ` is finite flat over `ℤ_ℓ`.
   (The twisting cocycle `β^{-1}a_σμ_σ` is unramified at `ℓ`.) Its determinant is the mod-`ℓ`
   cyclotomic character times a finite character unramified at `ℓ`, so `r̄_λ|_{I_ℓ}` is not
   trivial, and Serre's weight recipe for finite flat representations gives `k(r̄_λ) = 2`
   (Serre, Duke Math. J. 54 (1987), §2.8, UNCHECKED).
4. **Level.** The prime-to-`ℓ` Artin conductor `N(r̄_λ)` divides the conductor of `r_λ` at
   primes `p ≠ ℓ` (reduction does not increase the conductor exponent; Serre 1987, §1.2,
   UNCHECKED). The local bounds of lines 796-857 hold for `r_λ` at every `p ≠ ℓ`, and `ℓ ∉ T`
   contributes nothing. So `N(r̄_λ) ≤ QM²`.
5. **Serre's conjecture, strong form** (Khare–Wintenberger, Invent. Math. 178 (2009), with the
   level and weight optimization of Ribet, Edixhoven, Diamond, Buzzard and others that it
   invokes; STANDARD, exact theorem numbers UNCHECKED). For each `ℓ` as above there is a
   newform `f_ℓ` of weight 2 and level `N_ℓ ∣ N(r̄_λ)` with `ρ̄_{f_ℓ,λ'} ≅ r̄_λ`.
6. **Pigeonhole.** The newforms of weight 2 and level `≤ QM²`, with all their Galois conjugates,
   form a finite set. So one newform `f`, with one embedding of its coefficient field, serves
   for infinitely many `ℓ`. For `p ∉ T ∪ supp(N_f)`, the algebraic integer `t_p - a_p(f)` (in
   the compositum of `C` and the coefficient field of `f`) then lies in primes above infinitely
   many `ℓ`, so it is `0`.
7. **Conclusion.** `r_λ` and `ρ_{f,λ}` have the same traces at almost all Frobenius elements.
   `r_λ` is irreducible (its reduction is), so by Chebotarev and Brauer–Nesbitt
   `r_λ ≅ ρ_{f,λ}^{ss}` for every `λ`. Shimura's construction puts `ρ_{f,λ}` in `V_λ(A_f)`,
   a quotient of `J₁(N_f)`. The transfer step (lines 858-905) runs as before with
   `N = N_f ≤ QM²`.

This is Serre's 1987 argument (from residual modularity at infinitely many `ℓ` to `ℓ`-adic
modularity), which Khare–Wintenberger's theorem makes unconditional. The same argument is how
modularity of `GL₂`-type abelian varieties over `ℚ` is usually deduced from Serre's conjecture.

### 4.3 What changes in the trust base (VERIFIED against h-leaves §5.1)

| h-leaves §5.1 row | Present use | After §4.2 |
| --- | --- | --- |
| 9 (A008 at `ℓ = 3, 5`) | absolute irreducibility of `r_ℓ` | mod-`ℓ` Faltings for almost all `ℓ`, non-effective use (MW95 or Faltings–Zarhin); A063 (Hom theorem, transfer) unchanged |
| 10 (A009, crystalline form) | `r₅` potentially semistable, weights `0, -1`, for Pan | **removed**: only finite flatness of `A[ℓ]` at good `ℓ` is used (Raynaud 1974) |
| A010 (Berger) | de Rham implies potentially semistable | **removed** (already removed by h-leaves option (b)) |
| 11 (A011): Pan, Thm 1.0.4 | `ℓ`-adic modularity at `ℓ = 5` | **replaced** by Khare–Wintenberger 2009 (strong form) and the pigeonhole of step 6 |
| 11 (A011): Conrad / Serre 1968 | removing the twist, forcing weight 2 | **removed**: weight 2 and trivial twist come from the residual weight |
| 11 (A011): Li, Shimura | `r₅ ⊂ V(A_f)` | kept (Shimura's construction; Li for Fricke stability) |
| 17 (I1, Carayol) | level of `f` ≤ conductor | no longer a separate leaf: the level comes from `N(r̄_λ)`. Carayol's theorem is among the inputs of the strong form, so it stays in the trust base inside the citation |
| new | | Raynaud 1974 (finite flat models); Serre 1987 (definitions of `N(r̄)`, `k(r̄)`; conductor of a reduction) |

Constants. The bound `N ≤ QM²` is the same, Javanpeykar is applied to the same `N`, and the
transfer is unchanged. So `H₆(S;R)` and both Lean statements are unchanged (VERIFIED: the
constants of lines 858-964 depend on `N` only through `N ≤ QM²`).

Depth. Khare–Wintenberger use modularity lifting (Kisin) and potential modularity (Taylor), the
same circle of ideas as Pan's theorem. Depth is unchanged. What changes is the kind of the
input: one theorem from 2009 replaces a theorem from 2022 plus three `p`-adic Hodge theory inputs.
The statement of Serre's conjecture is also more elementary than Fontaine–Mazur (residual,
with an explicit level and weight), and its consequence used here is classical (Serre 1987, §4).

### 4.4 Other older routes, and why they do not apply (VERIFIED as arguments)

- **Langlands–Tunnell and 3-adic lifting** (the route of Wiles and BCDT). It needs `r̄_λ` with
  image in `GL₂(𝔽₃)`, which is solvable. The coefficient field of `r_λ` is the trace field
  `C`, generated by the values of `β` and the inner-twist data `a_σ`. It varies with `u`, so
  the residual image at a prime above 3 lies in `GL₂(𝔽_{3^f})` with `f` depending on `u`. It
  is solvable only when `f = 1`, so this route covers special fibres only, and its lifting step
  (Wiles, Taylor–Wiles, Diamond, Conrad–Diamond–Taylor) is again a modularity lifting theorem.
- **Ribet's level lowering alone** (Invent. Math. 100 (1990)). It lowers the level of a form
  already known to be modular, so it presupposes residual modularity.
- **A modular parametrization of `X⁶/W`.** `X⁶/W` has genus 0, and the Jacobians of the
  Shimura curves `X⁶_0(N)` are modular by Jacquet–Langlands and Ribet's isogeny
  (Ribet, Invent. Math. 100 (1990)). But the fibres `A_u` are *points* of the moduli curve, not
  quotients of its Jacobian. Modularity of `A_u` is a statement about each fibre separately, and
  no parametrization of the base curve gives it. VERIFIED as an argument.
- **Ribet–Pyle building blocks.** `A_u` is a building block (an abelian variety over `ℚ̄`
  isogenous to all its Galois conjugates, compatibly with `End⁰ = B`). Ribet (*Abelian varieties
  over ℚ and modular forms*, 1992; reprinted 2004) and Pyle show that building blocks are
  factors of `GL₂`-type varieties over `ℚ`, and those are modular by Serre's conjecture. This is
  rs-height R5.4: it uses the same Khare–Wintenberger input as §4.2 with a different route to
  the `G_ℚ`-representation, and the manuscript's own descent (lines 631-716) already does that
  part explicitly. Nothing is gained over §4.2.
- **Ellenberg–Skinner** (Duke Math. J. 109 (2001)) proved modularity of `ℚ`-curves under a
  semistability hypothesis at 3 before Khare–Wintenberger. An analogue for QM building blocks
  would need a semistability condition at 3 that the construction cannot impose on `A_u`
  (3 ∈ `S`, and `A_u` has bad reduction at 3 for many `u`). SPECULATIVE: an analogue for QM
  building blocks was not looked for in the literature.

So §4.2 is the one older modularity route that applies to every fibre. It does not reduce depth,
but it replaces the most recent input of H by a 2009 theorem and removes the `p`-adic Hodge
theory that only Pan's hypotheses needed.

### 4.5 The checks §4.2 still needs

1. Exact statement and numbering in Khare–Wintenberger 2009 (strong form, `ℓ > 2`, level
   `N(r̄)`, weight `k(r̄)`), and whether it includes the case `ℓ ∤ N(r̄)` with weight 2
   without further hypotheses.
2. Raynaud 1974 for the descent of finite flat models along `O_{L_v}/ℤ_ℓ` unramified, and
   Serre 1987, §2.8, for `k = 2` in the finite flat case with nontrivial inertia action.
3. A citable mod-`ℓ` Faltings statement for QM surfaces over number fields (semisimplicity and
   endomorphisms of `A[ℓ]` for almost all `ℓ`). If Faltings 1983 is cited, check that §5 of
   Faltings contains the mod-`ℓ` form; otherwise cite Zarhin or MW95 as h-leaves does.

## 5. Ranking of routes

| # | Route | Payoff | Main obstacle | First test and success criterion | Chance |
| --- | --- | --- | --- | --- | --- |
| 1 | Serre's argument at large `ℓ` in place of Pan (§4.2) | Medium. Removes Pan 2022, the de Rham comparison (A009), Berger (A010) and Conrad's local algebraicity. Carayol stops being a separate leaf. Constants unchanged | Pinning the exact statements: Khare–Wintenberger's strong form, Raynaud's finite flat descent, Serre's weight 2 for finite flat representations, a mod-`ℓ` Faltings theorem for almost all `ℓ` | Read Khare–Wintenberger 2009 and match each of steps 1-7 of §4.2 to a numbered statement, writing an audit record per step. Success: every step matched with no extra hypothesis (in particular none on the image of `r̄_λ` beyond absolute irreducibility, and `ℓ ∤ N(r̄)` allowed) | High. The argument is the standard deduction of modularity of `GL₂`-type varieties from Serre's conjecture, and every local input is already in the proof |
| 2 | Combine with h-leaves (NoCM, R5.1, R5.2 option (b)) | Small extra. With route 1, the `p`-adic Hodge theory leaves of h-leaves §5.1 row 10 disappear entirely, so R5.2 is no longer needed | None beyond route 1 | Recompute h-leaves' final table with route 1. Success: a table whose only deep inputs are Khare–Wintenberger, GR14, Shimura reciprocity and the Arakelov estimates | High |
| 3 | Split H into consumer-shaped hypotheses (§1.2) | Small. H_P may have any computable shape, and H_M any polynomial with exponent `< 25` (§1.3). The trust boundary shrinks to what is used | Pure refactor. It changes no mathematics, since no cheaper proof of either form is known | State `H_P^c` and `H_M^c` in Lean and derive both from `SixContactMin`. Success: `Main.lean` compiles with the two weaker hypotheses | High, but low value |
| 4 | A relative positivity test (Pos_K) (§3.5) | Very large. H would be replaced by the `S`-unit bound of Stewart–Yu (Baker), removing modularity, the Shimura curve and every leaf of H | No existential local device sees positive valuations at all primes, even relative to a label integer. Parity devices are blind to even valuations, and quadratic forms need a universal quantifier | Find an existential formula `D(t, K)` over `ℚ`, `K` a label integer, that is `ℚ_p`-insoluble whenever `v_p(t) = 2` and `p ∤ K` for all large `p`, and soluble at `(n, F(n))` for every integer `n`. Success: such a `D` with a completeness proof | Very low. It would be a new kind of Diophantine construction, comparable to the main theorem |
| 5 | Effective Shafarevich for QM surfaces without modularity | Large. Removes modularity from H | Lemma M forces complete moduli curves, where Baker's method has no `S`-unit equation to work on. The genus-two curve model degenerates at every contact prime (§3.3) | Find any effective (even exponential) height bound for QM surfaces over `ℚ̄` with good reduction outside `S`, not using modularity. Success: a published theorem or a proof sketch | Very low. No such result exists even for one fixed discriminant |
| 6 | Restrict the slopes to a thin set, or use rank-zero quotients (§2) | Would make H elementary on the restricted set | Every cheap restriction leaves twists of a compact curve of genus `≥ 2` or makes H false. All elliptic quotients of twists with a point have positive rank (131/131 points, 15/15 quotients) | Already run (`quotients.py`). Result: negative | Nil |
| 7 | Elliptic or genus-two families, or tests that add integrality at finitely many primes (§3.2-3.4) | Would replace H by Baker-type effective Shafarevich | Lemma C: every cusp has a positive-density set of approach primes, where the fibre is bad for every positive valuation | Already settled by Lemmas C and M and by `genus2cusp.py` (19/19 inputs degenerate) | Nil |

**Recommendation.** Do route 1, then route 2. Together they leave H resting on one modularity
theorem from 2009 (Khare–Wintenberger), one transcendence theorem (Gaudron–Rémond), Shimura
reciprocity and explicit Arakelov estimates, with unchanged constants. Removing H by a change of
construction needs a local test of a new kind (route 4). §3 shows that, short of such a test, the
family is forced up to the choice of a rational quaternionic Shimura curve, and then its height
bound is forced to go through modularity.
