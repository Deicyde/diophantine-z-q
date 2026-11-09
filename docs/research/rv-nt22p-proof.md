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
redundant hypotheses, and correct the plan of Lean changes in §5 of the note. That plan is
incomplete and partly wrong about which lemmas change, but it is correct about which lemmas need
new mathematics.

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
| 9 | Remark 1: the constant in `K_A ≈ |A| + 71` | wrong constant; harmless | cosmetic |
| 10 | Remark 3: Lemma P only on `S₀ = {2, 3, 5, 7, 13}` | CORRECT; can be strengthened | — |
| 11 | Plan of Lean changes (§3.2, §5 Route 1) | incomplete; partly wrong | minor |
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
  `η = 1`, `R₀` is **never** a square in `ℚ₂`. Then `v_2(1 − R₀q²)` is bounded (by at most
  `2e + 2`), and no choice of `q` absorbs the pole.

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
