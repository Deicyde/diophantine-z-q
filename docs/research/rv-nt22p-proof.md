# Referee report on Lemma P and the modified completeness argument of `nt-22p.md`

Scope: §3.2 of `docs/research/nt-22p.md` (Lemma P, field 2′, the modified choice of the witness
`q`) and §3.3 (Proposition AP and its remarks), checked against the 11/5 manuscript
`diophantine_zq.tex` (lines 1170–1190 and 1700–1758) and against the Lean definitions
`ZInQ.Mult.GoodSlope`, `slope_complete`, `pole_input_valuations`, `weak_approx_q`,
`tests_integral_old` and `ZInQ.PoleCompleteness`. Proposition D, Green–Tao 2008 and §4 of the note
are outside this report, except where §3.3 depends on them.

Notation is that of the note: `t = u/v` in lowest terms, `e = v_ℓ(v)`, `R₀ = ηF(t)/(t − 1)⁸`,
`a = 1 − R₀q²`, `α = v_ℓ(a)`, `R = ℓ₀²a²R₀`, `C_{gj} = D_{gj}/(R₀^{k_j}(t − 1)^{k_j+1})`,
`W_g = ∏_j(1 + RC_{gj}²)`, `Θ = Tr Σ_g W_g^{−1}`, `B = R/Θ²`, `E_ℓ = v_ℓ(ℓ₀)`.

## Verdict

**Proved after the listed repairs.** Lemma P (1)–(3), the modified completeness argument with
field 2′, Proposition AP and Remark 3 (Lemma P is needed only on `S₀`) are correct. I checked
each step by hand against the manuscript and the Lean source. An independent exact computation
confirms Lemma P(1) at `ℓ = 2` and Lemma P(3) on 30 samples, and a negative control shows that
its threshold is really used. None of the repairs below changes the argument. They correct one
false numerical statement (about `e = 1, 2` at the prime 2) and one wrong constant (`K_A`), drop
redundant hypotheses, and complete the plan of Lean changes in §5 of the note. That plan
leaves out several lemmas that must change, but it names the right lemmas as the ones needing new
mathematics.

## Findings

| # | Item | Verdict | Severity |
| --- | --- | --- | --- |
| 1 | Lemma P(1): `v_ℓ(R₀) = 2e`, `v_ℓ(t − 1) = −e`, `R₀ ∈ ℚ_ℓ^{×2}` | CORRECT | — |
| 2 | Lemma P(2): `v_ℓ(1 − R₀q²) ≥ N` on a non-empty open set | CORRECT | — |
| 3 | Lemma P(3): `v(RC²) ≥ 2α − 46e`, `v_ℓ(Θ) = v_ℓ(12)`, `v_ℓ(B) ≥ 4` | CORRECT | — |
| 4 | Test integrality `v_𝔩(D_{gj}) ≥ 0` above `S_b` is independent of `t` | CORRECT | — |
| 5 | The prime 2: `e ≥ 3` suffices; for `e = 1, 2` | CORRECT; the note's control statement understates | minor |
| 6 | Redundant hypotheses of Lemma P (seven numerators prime to `ℓ`) | not an error | cosmetic |
| 7 | Field 2′ and the modified choice of `q` (all five kinds of places) | CORRECT | — |
| 8 | Proposition AP (lowest terms, signs, fields 1, 2′, 3, 4) | CORRECT | — |
| 9 | Remark 1: the constant in the size of `K_A` | wrong constant; harmless | cosmetic |
| 10 | Remark 3: Lemma P only on `S₀ = {2, 3, 5, 7, 13}` | CORRECT; can be strengthened | — |
| 11 | Plan of Lean changes (§3.2, §5 Route 1) | incomplete | minor |
| 12 | Size of the poles actually needing Lemma P | observation | — |

Details follow, in the order of the table.

### 1. Lemma P(1) — CORRECT

With `η = 1`, `F(t) = ∏_{c∈𝒞}(u − cv)/v⁶` and `(t − 1)⁸ = (u − v)⁸/v⁸`, so
`R₀ = v² ∏_c(u − cv)/(u − v)⁸`. Since `0 ∈ 𝒞`, `u` is one of the six numerators and
`∏_c(u − cv) = u⁶ ∏_c(1 − cv/u)`. Hence `R₀ℓ^{−2e} = (vℓ^{−e})² u⁶ (u − v)^{−8} Π` with
`Π = ∏_c(1 − cv/u) ≡ 1 (mod ℓ^e)`. The first three factors are squares of `ℓ`-units, so
`v_ℓ(R₀) = 2e`. A unit `≡ 1 (mod ℓ)` is a square in `ℚ_ℓ` for odd `ℓ`, and a unit `≡ 1 (mod 8)`
is a square in `ℚ₂`. So `R₀ ∈ ℚ_ℓ^{×2}` for odd `ℓ`, and for `ℓ = 2` once `e ≥ 3`. Also
`v_ℓ(t − 1) = v_ℓ(u − v) − e = −e`.

The sign hypothesis `F(t) > 0` is used twice. It makes `η = 1` the sign chosen in
`slope_complete` (where `η` is fixed by `R₀ > 0`, needed at the real place). With `η = −1`,
`R₀` would be `−1` times a local square, which is a square only if `−1 ∈ ℚ_ℓ^{×2}`. That is
false for `ℓ = 2, 3, 7` (and true for `ℓ = 5, 13`, so the sign hypothesis could be dropped at
those two primes; this is not needed).

### 2. Lemma P(2) — CORRECT

With `q₀ = R₀^{−1/2} ∈ ℚ_ℓ`, `v_ℓ(q₀) = −e`, we have `1 − R₀q² = −R₀(q − q₀)(q + q₀)`. Near
`q₀`, `v_ℓ(q + q₀) = −e + v_ℓ(2)`, so `v_ℓ(1 − R₀q²) = e + v_ℓ(2) + v_ℓ(q − q₀)`, which is
`≥ N` on the ball `v_ℓ(q − q₀) ≥ N − e − v_ℓ(2)`. In integer form, with `q = w/ℓ^e`, one needs
`w² · R₀ℓ^{−2e} ≡ 1 (mod ℓ^{N'})`, and such `w` exists for every `N'`.

### 3. Lemma P(3) — CORRECT

The test values `D_{gj}` do not depend on `t` (see finding 4), and the normalization divides by
`R₀^{k_j}(t − 1)^{k_j+1}`, so at a place `𝔩 | ℓ` (valuation extending `v_ℓ`)
`v(C_{gj}) = v(D_{gj}) − k_j·2e + (k_j + 1)e = v(D_{gj}) − e(k_j − 1) ≥ −e(k_j − 1)`.
With `v(R) = 2E_ℓ + 2α + 2e`, this gives `v(RC_{gj}²) ≥ 2E_ℓ + 2α + 4e − 2ek_j`. That is
`2E_ℓ + 2α + 2e` for `k_j = 1` and `2E_ℓ + 2α − 46e` for `k_j = 25`; with `E_ℓ ≥ 0` both are
`≥ 2α − 46e`. These are the exponents of the manuscript (line 1185: `k_j = 1` for `j ≤ 8`,
`k_j = 25` for `9 ≤ j ≤ 12`; Lean `prec`). If `α ≥ 23e + v_ℓ(12) + 2`, then
`2α − 46e ≥ 2v_ℓ(12) + 4 > v_ℓ(12)`.

Each factor `1 + x` of `W_g` then has `v(x) > v_ℓ(12) ≥ 0`. So `W_g = 1 + w_g` and
`W_g^{−1} − 1 = −w_g/(1 + w_g)`, both of valuation `> v_ℓ(12)`. Since `Tr 1 = 2`,
`Θ = 12 + Tr y` with `y = Σ_g(W_g^{−1} − 1)`. If `ℓ` splits in `K₀ = ℚ(√2)` (here `ℓ = 7`), the
two embeddings of `K₀` into `ℚ_ℓ` correspond to the two places, and `v_ℓ(Tr y)` is at least the
minimum of `v_{𝔩₁}(y)` and `v_{𝔩₂}(y)`. If `ℓ` is inert or ramified (`ℓ = 3, 5, 13`, resp.
`ℓ = 2`), conjugation preserves the unique place. In both cases `v_ℓ(Θ − 12) > v_ℓ(12)`, hence
`v_ℓ(Θ) = v_ℓ(12)`. At the ramified prime the place valuations lie in `½ℤ`, but `Tr y` is
rational, so the strict inequality survives. Finally
`v_ℓ(B) = 2E_ℓ + 2α + 2e − 2v_ℓ(12) ≥ 46e + 4 ≥ 4`.

Two remarks on this step:

- In Lean, `v_π` at `π | ℓ` in `ℤ[√2]` is normalized so that `v_π(ℓ) = e(π | ℓ)`. That is
  `vP π hπ` with `exists_vP_ratCast`, as in part 1 of `pole_input_valuations`. The hypothesis
  `v ≥ 0` does not depend on the normalization, and the inequalities only scale by
  `e(π | ℓ) ∈ {1, 2}`.
- With the true `E_ℓ = 52C_ℓ + v_ℓ(12) + 4`, the bound becomes
  `v_ℓ(B) ≥ 104C_ℓ + 8 + 2α + 2e > 103C_ℓ + 8`. So the conclusion of part 1 of
  `pole_input_valuations` survives unchanged in the new branch (finding 11).

### 4. Integrality of the tests when `t` has a pole — CORRECT

In `slope_complete` the test values are `D g j = testValues (h g) (z g) c`, with
`z g = (n_i · h g)_i` and `c = certShifts (n₁, n₂, n₁n₂)`. They depend on the shifts `h g`
and the indices only. The slope `t` enters through the selected primes, which determine the
shifts, but not through the values themselves. `tests_integral_old` (`SbIntegrality.lean:98`)
has the hypotheses `M₀ | h`, `h ≠ 0`, `h ≠ c_*`, `p ∈ S_b`, `π | p`, and none of them mentions `t`.
These hypotheses hold for every group: the shifts of `exists_shift` at selected primes satisfy
them, and so does the default shift `h = 2c_* = 8M₀` of the unused groups. So `v_𝔩(D_{gj}) ≥ 0`
holds at every place above `S_b`, whatever the valuations of `t` there (manuscript lines
1727–1728: "the small formal subgroup in the definition of `M₀` gives `v_p(D_{gj}) ≥ 0` at
`S_b`"). The witnesses `η, q, h, z` of the slope predicate are otherwise unconstrained, and `q`
enters the predicate only through `a` (`SlopePred`, `SlopePredicate.lean:52`).

### 5. The prime 2 — CORRECT; one false statement in the note

At `ℓ = 2`, `v_2(cv/u) = e + v_2(c)` with `v_2(c) ∈ {∞, 0, 2, 3, 1, 2}`. Since
`Σ_c c = −149` and `e₂(𝒞)` is even (only `−15` is odd), one gets
`Π ≡ 1 + 2w (mod 8)` with `w = v/(2u)` odd if `e = 1`, and `Π ≡ 1 + 4 ≡ 5 (mod 8)` if `e = 2`.
The other factors of `R₀2^{−2e}` are odd squares. Hence:

- for `e ≥ 3`, `Π ≡ 1 (mod 8)` and `R₀` is a 2-adic square;
- for `e = 1`, the class of `R₀2^{−2e}` mod 8 is `3` or `7`, and for `e = 2` it is `5`; with
  `η = 1`, `R₀` is **never** a square in `ℚ₂`. Then `v_2(1 − R₀q²) ≤ 2` for every `q`:
  the valuation of `R₀q²` is even, and when it is `0` the unit `R₀q²` is `≡ 3, 5, 7 (mod 8)`,
  so `1 − R₀q²` has valuation 1 or 2. No choice of `q` absorbs the pole.

I checked this exhaustively over `u` mod `2^{e+6}` and odd `w < 64`, for `e = 1, …, 6`. The
square classes are `{3, 7}`, `{5}`, `{1}`, `{1}`, `{1}`, `{1}`.

The note's control ("with `v₂(v) ≤ 2`, `R₀` is often not a square in `ℚ₂`, 22 non-squares among
the valid samples") should say *never*. This does not affect the argument: `e ≤ 2 < B₂ = 4`, so
field 2 holds at 2 and the old argument applies. In Proposition AP the Lemma P branch at 2 is
used only for `e ≥ 5`.

### 6. Redundant hypotheses — cosmetic

If `e = v_ℓ(v) ≥ 1` and `gcd(u, v) = 1`, then `u − cv ≡ u` and `u − v ≡ u (mod ℓ)` are
automatically `ℓ`-units. The hypothesis "the seven numbers are prime to `ℓ`" is therefore
implied by `e ≥ 1`. For rational `t` the whole hypothesis is just `v_ℓ(t) = −e < 0`. Indeed
`v_ℓ(t − c) = v_ℓ(t)` for every integer `c`, so `v_ℓ(F(t)) = 6v_ℓ(t)`,
`v_ℓ(t − 1) = v_ℓ(t)` and `v_ℓ(R₀) = −2v_ℓ(t)`, without reference to `u, v`. The second
alternative of field 2′ can be stated as
`v_ℓ(t) < 0 ∧ F(t) > 0 ∧ (ℓ = 2 → v_2(t) ≤ −3)`. This is also the convenient form for Lean.

### 7. Field 2′ and the modified choice of `q` — CORRECT

Let `t` satisfy fields 1, 2′, 3, 4. Let `S_pole ⊂ S_b` be the primes where the second
alternative of 2′ is used, `P` the odd contact primes outside `S_b`, and
`N_ℓ = 23e_ℓ + v_ℓ(12) + 2`. If `S_pole ≠ ∅` then `F(t) > 0`, so the sign chosen in
`slope_complete` is `η = 1`. That choice is forced by `R₀ > 0` and is the one Lemma P needs: the
real place and the places of `S_pole` ask for the same `η`. The positivity lemma
`pole_input_small` gives `ε > 0` depending on `R₀`, `ℓ₀` and the normalized tests only, not on
`q`. The open conditions on `q` are then:

1. at `ℓ ∈ S_pole`, `q` lies in the ball of Lemma P(2) for `N_ℓ`, a ball of radius
   `ℓ^{−(N_ℓ − e − v(2))}` around `±R₀^{−1/2}`;
2. at `ℓ ∈ S_b ∖ S_pole`, `v_ℓ(q) ≥ C_ℓ` (as now);
3. at `p ∈ P`, `v_p(q) ≥ 0` (as now);
4. at the real place, `|q − R₀^{−1/2}| < δ` and `q ≠ ±R₀^{−1/2}` (as now).

These are finitely many non-empty open conditions at distinct places, so weak approximation
gives `q ∈ ℚ`. Concretely, take `q = m/(L ℓ′^k)` with `L = ∏_{ℓ∈S_pole} ℓ^{e_ℓ}` and `ℓ′` a prime
outside `S_b ∪ P`. Then `m` is fixed modulo `M = ∏_{S_pole} ℓ^{N_ℓ+1} ∏_{S_b∖S_pole} ℓ^{C_ℓ}`.
The residue at `ℓ ∈ S_pole` is `w_ℓ · (L/ℓ^{e_ℓ}) · ℓ′^k`, which depends on `k`. Fixing `k`
first, the admissible `q` form a coset of `(M/(Lℓ′^k))ℤ` in `ℚ`, whose spacing tends to `0`.
With this `q`, the place-by-place check is:

- `ℓ ∈ S_pole`: Lemma P(3) (finding 3) gives `v_ℓ(B) ≥ 46e + 4 ≥ 4`, in fact `≥ 103C_ℓ + 8`.
- `ℓ ∈ S_b ∖ S_pole`: field 2 holds there and `v_ℓ(q) ≥ C_ℓ`, so `a` is an `ℓ`-unit, and part 1 of
  `pole_input_valuations` applies verbatim: `v_ℓ(B) ≥ 103C_ℓ + 8`.
- `p ∈ P`: `v_p(R₀) = 1` and `q` is `p`-integral, so `a ≡ 1 (mod p)`, `v_p(R) = 1`, and part 2
  gives `v_p(B) = 1`. Nothing here depends on the old primes.
- Other finite primes, including `ℓ′`: part 3 gives `v_p(B) ≡ v_p(F(t)/(t − 1)⁸) ≡ 0 (mod 2)`.
  This holds because `a` enters `R` squared and `Θ ∈ ℚ` enters `B` squared, so the parity does
  not depend on `q`. The evenness of `v_p(F(t)/(t − 1)⁸)` at `p ∉ S_b ∪ P` is
  `even_padicValRat_contactQuot` and uses field 3 only. In particular `ℓ′ ∉ P` is all that is
  needed of the auxiliary prime.
- Real place: as before, `0 < |a| < ε` gives `W_g > 0`, `Θ > 0` and `0 < B < 1/2`, together with
  all the non-vanishing guards.

So `B` has square reduced denominator, `0 < B < 1/2` and `v_p(B) ≥ 4` on `S₀ ⊂ S_b`, which are
exactly the hypotheses of `PoleCompleteness` (`Hypotheses/Pole.lean:62`; manuscript Theorem 5.2,
line 1001). The polynomial, the slope predicate and soundness are untouched: field 2′ is a
condition on the slopes produced by the completeness proof, not on the predicate.

### 8. Proposition AP — CORRECT

With `T = 𝒞 ∪ {1}`, `S⁺ = T ∪ (A′ − T)` and `u = x + (max S⁺)v`, each `u − c′v`
(`c′ ∈ S⁺`) is the term of index `max S⁺ − c′ ∈ [0, K_A]`.

- *Lowest terms*: a common prime of `u` and `v` divides `x`, hence every term. The terms are
  distinct primes (`v ≥ 1`), which is impossible. Also `gcd(A′v − u, v) = gcd(u, v) = 1`.
- *Signs*: `t₁ = max S⁺ + x/v > 1 > 0` (here `x ≥ 1` is used), so all six factors of `F(t₁)`
  are positive. Next, `max S⁺ = max(1, A′ + 60)`. If `A′ + 60 ≥ 1` then `t₂ = −60 − x/v < −60`.
  Otherwise `t₂ = A′ − 1 − x/v < A′ − 1 < −60`. Either way all six factors of `F(t₂)` are
  negative and `F(t₂) > 0`.
- *Field 1*: `t₁ − c = (u − cv)/v` and `t₂ − c = −(u − (A′ − c)v)/v` are nonzero, and so are the
  analogous expressions for `c = 1`.
- *Field 2′*: all fourteen numbers are primes `> max S_b`, hence `ℓ`-units for `ℓ ∈ S_b`. If
  `e = 0`, both valuations of field 2 vanish. If `1 ≤ e ≤ B_ℓ`, field 2 holds
  (`|v_ℓ(t − 1)| = e ≤ B_ℓ` and `|v_ℓ(R₀)| = 2e ≤ 8B_ℓ`). If `e > B_ℓ`, the alternative of 2′
  holds; at `ℓ = 2` this means `e ≥ 5 ≥ 3`. Since the condition `|v_ℓ(t − 1)| ≤ B_ℓ` reads
  `e ≤ B_ℓ` here, field 2 holds exactly when `e ≤ B_ℓ`.
- *Fields 3, 4*: an odd contact prime `p ∉ S_b` of `t₁` has `v_p(u − cv) > v_p(v)`, so `p ∤ v`
  (a prime dividing `v` gives `v_p(t₁ − c) = −v_p(v) < 0`) and `p | u − cv`, a prime. So `p` is that
  prime, which lies in `G`, has valuation 1 and exceeds `max S_b ≥ 0 = B₀`. There are at most six
  such primes. The same holds for `t₂`. These are the arguments of `goodSlope_of_primeValues`
  (`TwoSlope.lean:41`) without its hypothesis `hold`.
- *Constant slope*: `goodSlope_neg_ten` gives field 2 for `−10`, hence 2′.

### 9. Remark 1 — wrong constant, harmless

For `A′ ≥ −59`, `max S⁺ = A′ + 60` and `min S⁺ = −60`, so `K_A = A + 130`. For `A′ ≤ −60`,
`K_A = 2 − A′ = −A − 8`. (For example, `A = 0` gives `S⁺ ⊂ [−60, 70]` and `K_A = 130`.) So
`K_A = |A| + O(1)`, but not `≈ |A| + 71`. The remark only uses that `K_A → ∞`.

### 10. Remark 3: Lemma P is needed only on `S₀` — CORRECT, and can be strengthened

`PoleCompleteness` asks for `v_p(B) ≥ 4` only on `S₀`. Elsewhere it asks only that `B` have a
square reduced denominator, that is, that every negative `v_p(B)` be even. At `ℓ ∈ S_b ∖ S₀`,
`v_ℓ(B) = 2(E_ℓ + α − v_ℓ(Θ)) + v_ℓ(R₀)`. In the progression form `v_ℓ(R₀) = 2e`, so `v_ℓ(B)` is
even for every `q` and every test values. CORRECT. No condition on `q` is needed at those
primes, and the catalogue primes (`B_ℓ = 1`) never need Lemma P.

The same computation gives a stronger statement. Since
`v_ℓ(R₀) ≡ v_ℓ(F(t)) (mod 2)`, field 2 at `ℓ ∈ S_b ∖ S₀` can be replaced by the single condition
"`v_ℓ(F(t))` is even", with no bound at all. Field 2 at those primes is used nowhere else in the
completeness proof: `GoodSlope.old` is consumed only in part 1 of `pole_input_valuations`
(`PoleValuations.lean:126`), and part 1 is used only for the `S₀` bound and for the
square-denominator conclusion. With this change field 2′ becomes:

> **2″.** For `ℓ ∈ S₀`: field 2 holds at `ℓ`, or `v_ℓ(t) < 0`, `F(t) > 0` and
> (`ℓ = 2 ⇒ v_2(t) ≤ −3`). For `ℓ ∈ S_b ∖ S₀`: `v_ℓ(F(t))` is even.

This makes the Lean change smaller: Lemma P and the residue-class weak approximation are needed
at five primes only, and part 1 of `pole_input_valuations` splits into an `S₀` part and an
evenness part.

### 11. Which Lean lemmas change — the note's plan is incomplete

The note lists three changes: `GoodSlope.old`, `slope_complete`/`pole_input_valuations`, and
`weak_approx_q`. The full list, from reading the consumers, is as follows. The first five need new
mathematics or a real change of proof; the others need a one-line adaptation or none.

1. **New lemma (Lemma P(1)–(2), integer form).** For a prime `ℓ`, `t ∈ ℚ` with `v_ℓ(t) = −e < 0`,
   `F(t) > 0` and (`ℓ = 2 ⇒ e ≥ 3`), and every `N`, there is `w ∈ ℤ` with
   `v_ℓ(1 − R₀(w/ℓ^e)²) ≥ N` for `R₀ = F(t)/(t − 1)⁸`. A short route is to apply Mathlib's
   `hensels_lemma` in `ℤ_[ℓ]` to `X² − Π` at `X = 1`. Its hypothesis `‖Π − 1‖ < ‖2‖²` is
   `ℓ^{−e} < 1` for odd `ℓ` and `2^{−e} < 1/4`, i.e. `e ≥ 3`, at `ℓ = 2`. This is exactly the
   dichotomy of finding 5. The other factor `(vℓ^{−e})u³(u − v)^{−4}` of `(R₀ℓ^{−2e})^{1/2}` is
   explicit.
2. **`weak_approx_q`** (`WeakApproximation.lean:29`). Add a variant with a third finite set of
   primes, carrying exponents `e_ℓ`, precisions `N_ℓ` and integer targets `w_ℓ`, with conclusion
   `v_ℓ(qℓ^{e_ℓ} − w_ℓ) ≥ N_ℓ`. In the grid proof the residue of the numerator modulo `ℓ^{N_ℓ}`
   depends on the power `ℓ′^k` of the auxiliary prime (finding 7). So `k` must be fixed before
   the residue is computed, and the grid is a coset `r_k + Mℤ`, not `Mℤ`. The existing lemma can
   stay for the other callers.
3. **`pole_input_valuations`** (`PoleValuations.lean:62`). Replace the hypothesis `hq_old` by a
   per-prime disjunction: `(field 2 at p ∧ C_p ≤ v_p(q)) ∨ (v_p(t) < 0 ∧ 23(−v_p(t)) + v_p(12) + 2 ≤ v_p(a))`.
   Part 1 gets a second branch, which is the computation of finding 3: `hva` is replaced by
   `v_p(a) ≥ N_p`, and `v_p(R₀) = −2v_p(t)`, `v_p(t − 1) = v_p(t)` follow from `v_p(t) < 0`.
   That branch needs neither `η = 1` nor the square root. The **conclusions can stay as they
   are**, including `103C_p + 8 ≤ v_p(B)` on `S_b`. Parts 2 and 3 are unchanged. Under 2″
   (finding 10), part 1 is instead stated on `S₀`, with an evenness clause on `S_b ∖ S₀`.
4. **`slope_complete`** (`SlopeCompleteness.lean:75`). Compute `S_pole` and the targets
   `w_ℓ` (item 1), call the new weak approximation (item 2), and feed item 3. It needs a small
   lemma that the sign chosen by `R₀ > 0` is `η = 1` when `contactPoly t > 0`. Item 3's
   `v_p(a) ≥ N_p` follows from `v_ℓ(qℓ^e − w) ≥ N` by the identity of Lemma P(2).
5. **New** `slopeRepresentation_of_goodPrimeAP`, with a constructor `goodSlope_of_progression`.
   The existing `goodSlope_of_primeValues` (`TwoSlope.lean:41`) cannot be reused as it stands:
   its hypothesis `hold` (`v_q(v) ≤ B_q` and `v_q(u − v) ≤ B_q` on `S_b`) is exactly what fails
   for progressions. Its proof of fields 1, 3, 4 can be reused. Field 2′ needs the case split of
   finding 8.
6. **`GoodSlope`** (`PatternSlopes.lean:26`). Field `old` becomes the disjunction 2′ (or 2″).
   `GoodSlope.old_le_Cp` has no users and can be deleted or restated under the first alternative.
7. **Constructors of the old kind** need one `Or.inl` each: `goodSlope_of_values` (`PatternSlopes.lean:113`),
   hence `pattern_slopes` and `slopeRepresentation_of_fixedPrimePattern`; `goodSlope_of_primeValues`,
   `goodSlope_neg_ten` and `slopeRepresentation_of_twoSlopePattern` (`TwoSlope.lean`). The present
   main theorems from 22P and 22P₂ therefore survive.
8. **Hypotheses and assembly.** Add the hypothesis `GoodPrimeAP` (`Hypotheses/PrimePattern.lean`)
   and a main-theorem variant (`Main.lean`).
9. **Unchanged.** `tests_integral_old`, `tests_precision_selected`, `exists_shift`,
   `padicValRat_contactQuot_eq_one` and `even_padicValRat_contactQuot` (`PoleValuationsAux.lean`),
   `pole_input_small`, and the consumers of `SlopeRepresentation` (`Core.lean`,
   `Template.lean`, `Top/Exact.lean`, `Assembly/Top/*.lean`). These never destructure
   `GoodSlope`.

An alternative with less churn is to leave `GoodSlope` alone and add `GoodSlope′`. One would then
prove `GoodSlope → GoodSlope′`, state `slope_complete` for `GoodSlope′`, and let
`SlopeRepresentation` quantify over `GoodSlope′`. Either way the work is items 1–5.

### 12. How large must a pole be before Lemma P is needed? — observation

With the actual normalization `E_ℓ = 52C_ℓ + v_ℓ(12) + 4`, the old argument (`v_ℓ(q)` large, so
`α = 0`) already works whenever `v(RC²) ≥ 2E_ℓ − 46e > v_ℓ(12)`. That is the case for
`e ≤ 126` on `S_ht` (`C_ℓ = 56`) and `e ≤ 31` on the catalogue (`C_ℓ = 14`), and then
`v_ℓ(B) = 2E_ℓ + 2e − 2v_ℓ(12) ≥ 4`. The bounds `B_ℓ` of field 2 are therefore far from sharp.
This does not make Lemma P superfluous: Green–Tao gives no bound at all on `v_ℓ(v)`, and by
Remark 1 the poles at the small primes grow with `|A|`. It does show that, mathematically, the
new branch is needed only for poles of order above 126 at the primes of `S₀`; the threshold
`e > B_ℓ = 4` in field 2′ is a convenience. The old bound also gives an easy sanity check for a
Lean statement of the branch: the two branches must agree for `5 ≤ e ≤ 126`.

## Numerical checks

All computations used exact arithmetic in `ℚ(√2)` and an implementation independent of the
note's scripts (`scratch/rv-nt22p-proof/lemmaP_check.py`, output `lemmaP_check.out`).

- *Square classes at 2* (exhaustive; finding 5): the class of `∏_c(u − cv)` mod 8 for
  `v_2(v) = e` is `{3, 7}`, `{5}`, `{1}`, `{1}`, `{1}`, `{1}` for `e = 1, …, 6`.
- *Lemma P(3)*, 30 samples. Each sample is a slope with poles at all five primes of `S₀`
  (`e₂ ∈ [3, 8]`, other `e_ℓ ∈ [1, 5]`) and `F(t) > 0`. One rational `q` was built by the Chinese
  remainder theorem from Hensel roots, with `α_ℓ ≥ 23e_ℓ + v_ℓ(12) + 2`. There were 72 random
  test values `D_{gj} ∈ ℤ[√2]`, and `ℓ₀ = 1` (the worst case `E_ℓ = 0`). Results, out of 30:
  `α_ℓ ≥ N_ℓ` at all five primes in 30; `v_ℓ(Θ) = v_ℓ(12)` in 30;
  `v_ℓ(B) = 2α_ℓ + 2e_ℓ − 2v_ℓ(12)` exactly in 30; `v_ℓ(B) ≥ 4` in 30.
- *Negative control*, 30 samples: the root was perturbed so that `α_ℓ = 19e_ℓ < 23e_ℓ`. Then
  `v_ℓ(Θ)` is large and `v_ℓ(B)` is very negative at every prime in every sample. So with
  `E_ℓ = 0` the threshold `2α − 46e > v_ℓ(12)` is not slack.

## Repairs

None of these changes the mathematics of §3.2–3.3. With them the modified completeness argument
and Proposition AP are proved.

1. **(Finding 5.)** Replace the control sentence of §3.2 by: "for `v₂(v) ∈ {1, 2}` and `η = 1`,
   `R₀` is never a square in `ℚ₂`. The unit `R₀2^{−2e}` is `≡ 3, 7 (mod 8)` for `e = 1` and
   `≡ 5 (mod 8)` for `e = 2`, so `v₂(1 − R₀q²) ≤ 2` for all `q`. These cases are covered by
   field 2, since `e ≤ 2 < B₂`."
2. **(Finding 6.)** State Lemma P and the second alternative of field 2′ with the hypothesis
   `v_ℓ(t) = −e < 0` (plus `F(t) > 0`, and `e ≥ 3` if `ℓ = 2`), and note that the seven
   numerators are then automatically `ℓ`-units.
3. **(Finding 9.)** In Remark 1 replace `K_A ≈ |A| + 71` by `K_A = A + 130` for `A ≥ −69` and
   `K_A = −A − 8` for `A ≤ −70`.
4. **(Finding 10, optional.)** Use 2″ in place of 2′: Lemma P on `S₀` only, and at
   `ℓ ∈ S_b ∖ S₀` only the parity condition "`v_ℓ(F(t))` even". This shortens the Lean work and
   removes the need to discuss the catalogue primes.
5. **(Finding 11.)** Replace the three-item Lean plan of §5, Route 1, by the list of finding 11.
   In particular: the conclusions of `pole_input_valuations` need not change;
   `goodSlope_of_primeValues` must be replaced, not reused, for progressions; the residue
   class in the new weak approximation depends on the power of the auxiliary prime; and Lemma
   P(1)–(2) follows from `hensels_lemma` applied to `X² − Π` at `1`, whose hypothesis is exactly
   "`ℓ` odd, or `e ≥ 3`".
6. **(Finding 7, presentation.)** In the list "the modified completeness argument", add that the
   real place and the places of `S_pole` require the same sign `η = 1`, and that this is why
   `F(t) > 0` belongs to field 2′. Also add that `ℓ′ ∉ P` is the only condition on the auxiliary
   prime of the weak approximation.

## What this report does not cover

Proposition D (positive density of `G`), the application of Green–Tao 2008, and §4 of the note
were not examined. Proposition AP was checked as an implication from 22P_AP. The constant slope
`−10` was taken from `goodSlope_neg_ten`, which is kernel-checked. No Lean code was written or
run: the statements in finding 11 come from reading the source.
