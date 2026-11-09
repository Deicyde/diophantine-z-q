# Referee report on the proof of the descent lemma in `slot-k.md` §2

This report checks the proof of the descent lemma DL given in `docs/research/slot-k.md` §2: the
configurations and the use of Proposition 0 (§2.1), the two gluing lemmas (§2.2), the base
configuration (§2.3), the slots (§2.4), the proof of DL (§2.5) and the count (§2.6). It also checks
that DL, as proved, is the statement that Route K needs. Every step was redone by hand. The
computations below are independent implementations: none imports the code of `scratch/slot-k/`
or `scratch/descent-alt/`.

Each examined step is marked **CORRECT** (checked here), **GAP** (missing or wrong) or
**UNCHECKED**.

## Verdict

**DL is proved as written.** I found no mathematical gap in §2. Every cancellation and every sign
in Lemmas 1–3 and in steps 0–6 of the theorem is right, the residue conditions on the auxiliary
primes are always simultaneously satisfiable, and the conclusion is exactly what the `x + ℓ`
version of the pole polynomial needs, once a certificate of Selmer type is turned into a rational
point by the deep input (Kriz's rank-one 2-converse with the corank lemma).

The findings are all minor. None affects the validity of DL:

| # | Severity | Where | Finding |
| --- | --- | --- | --- |
| 1 | minor (inaccurate commentary) | §2.4, §2.5 "What each slot does" | The condition `[q₀/ℓ] = 0` for `ℓ ∈ T` is never used. Symbols between `q₀` and `T` lie inside the glued set of step 5 and drop out of Lemma 2. The note says they are "dictated by the transfer to the second curve"; they are free. |
| 2 | minor (overstatement) | introduction, §2.6 | "Within one of the lower bound of Proposition B" holds only when `ω(β) = k + 1`. In general the construction uses `ω(β)` auxiliary primes for the first curve, against the lower bound `k ≤ ω(β) − 1`. |
| 3 | minor (wording) | §2.1, "Odd places and the real place" | The sentence "classes are automatically unramified outside `2d∞`, since they are supported on `−1, 2` and the primes of `d`" states the easy direction. The proof needs both directions: Selmer classes are unramified outside `2d∞` (Silverman X.1.4), so they are supported on `−1, 2` and the primes of `d`; conversely such classes satisfy the local conditions at every `p ∤ 2d` automatically. Both are standard. |
| 4 | minor (citation) | §1.2, §4.1 | Kriz's Theorem 10.17(2) sits under header hypotheses belonging to its part (1); pc-audit RK1 recommends citing Theorem 10.13 directly. Kriz's standing assumption `f₀ ≥ 4` should be checked explicitly; here it is immediate, since `f₀ = |n|` or `|n|θ` and `|n| ≥ 7·3 = 21`. |
| 5 | minor (presentation) | §1.2 | The torsion certificate is phrased loosely ("`(β, 0)` or `(−β, 0)` lies on `C_d` up to the identification"). The construction never produces a torsion certificate, so this is immaterial to DL. |

No repair is needed for the proof. Findings 1–5 are editorial. The repairs section lists the
suggested rewordings.

**Marks, step by step.**

| Step | Mark | Section here |
| --- | --- | --- |
| (θ1)–(θ4) | CORRECT | §1 |
| Step 0 (multiplier), for every eligible `m` | CORRECT | §1 |
| Proposition 0: odd places, primes `∤ 2d`, real place | CORRECT | §2 |
| Proposition 0: place-2 row for `c = 5`; structure of the place-2 rows | CORRECT | §2 |
| Proposition 0: place-2 rows for `c = 1, 3, 7` | not used; consistent with an exact descent on 30 curves | §2, §6 |
| Lemma 1 | CORRECT | §3 |
| Lemma 2, steps 1–4, (2.1), (2.2), bijectivity | CORRECT | §3 |
| Lemma 3 | CORRECT | §4 |
| Existence of the slots (CRT, reciprocity, Dirichlet, edge cases) | CORRECT | §5.1 |
| Steps 1–6 of the theorem | CORRECT | §5.2 |
| Count `ω(β) + ω(θ)` | CORRECT | §7 |
| Comparison with Proposition B | overstated (finding 2), not used | §7 |
| DL ⟹ points on `C_n`, `C_{nθ}` with abscissa in `βℚ*²` (given Kriz) | CORRECT | §8 |
| Points ⟹ zero of the `x + ℓ` pole polynomial | CORRECT | §8 |
| Kriz's Theorem 10.13 itself | UNCHECKED (outside scope) | §8 |

## 1. The inputs (§1.1 of the note)

Notation is that of the note: `C_d : y² = x³ − d²x`, Kummer map `P ↦ (x, x − d)`, `[x/p] ∈ 𝔽₂`
the bit of the Legendre symbol, `λ_p = [−1/p]`, `μ_p = [2/p]`, `β = sqf(mB)`, `θ = sqf(m(m − B))`.

**(θ1)–(θ4).** CORRECT. Since `mB = β k²` and `m(m − B) = m²(1 − B/m)`, one has `βt² = B/m` and
`θc² = 1 − βt²` with `t = k/m`. For `p | m` (so `p ∈ S₀`), `v_p(B/m) = v_p(B) − 1 ≥ 3`; for
`p ∈ S₀`, `p ∤ m`, `v_p(B/m) ≥ 4`; for `p ∉ S₀` a negative `v_p(B/m) = v_p(B)` is even, because the
reduced denominator of `B` is a square.

- At `2` and at `3, 5, 7, 13`, `v_p(βt²) ≥ 3`, so `1 − βt²` is a `2`-adic unit `≡ 1 (mod 8)`, resp.
  a `p`-adic unit square. Hence `θ` is odd, `θ ≡ 1 (mod 8)` and `gcd(θ, 2730) = 1`. Also
  `1 − B/m > 0` because `|B/m| ≤ B < 1/2`, so `θ > 0`.
- At an odd `p | β`, `v_p(βt²)` is odd, hence not negative and even, hence positive (for
  `p ∈ S₀` it is `≥ 3` anyway). So `1 − βt²` is a `p`-adic unit square: `p ∤ θ` and `(θ/p) = 1`.
- At `ℓ | θ` (so `ℓ ∉ S₀`), `v_ℓ(1 − βt²)` is odd. If `v_ℓ(βt²) > 0` it would be `0`; if
  `v_ℓ(βt²) < 0` it would be `v_ℓ(B)`, which is then even. So `βt²` is an `ℓ`-adic unit with
  `βt² ≡ 1 (mod ℓ)`, and `(β/ℓ) = 1` for the **signed** `β`. This sign is what step 6 uses.

**Step 0 (multiplier, §2.4).** CORRECT. `v₂(β) ≡ v₂(B) + v₂(m)`, so one parity of `v₂(m)` makes `β`
odd. Then `|β| ≡ |m_odd| · b (mod 8)`, with `b` the odd squarefree kernel of `B`: the two differ by
the square of the odd number `gcd(m_odd, b)` and by odd squares. The odd divisors `1, 3, 5, 7` of
2730 cover `(ℤ/8)*`, and the sign of `m` is free. For each admissible `B` exactly 8 of the 64
signed divisors give `β` odd with `|β| ≡ 7 (mod 8)`: `v₂(m)` is forced, the 16 odd divisors of 2730
fall four into each class of `(ℤ/8)*`, and both signs are allowed. Every one of them satisfies
(θ1)–(θ4), and the proof uses nothing else about `m`, so the construction works for whichever
eligible `m` is picked.

## 2. Configurations and Proposition 0 (§2.1)

The proof applies Proposition 0 only to the two actual curves `C_{d₁}`, `C_{d₂}`, with
`d₁ = |n|`, `d₂ = d₁θ`. All other configurations are abstract linear systems, and Lemmas 1–3 are
statements of linear algebra about them. Both `d₁` and `d₂` are `≡ 5 (mod 8)`: `|β| ≡ 7`,
`q₀ ≡ 3`, every glue prime `≡ 1` and `θ ≡ 1 (mod 8)`. So only the odd places, the real place and the
place-2 row for `c = 5` are needed. I rederived all three.

**Odd `p | d`.** CORRECT. Since `p` is odd and `E[2] ⊆ E(ℚ_p)`, `#E(ℚ_p)/2E(ℚ_p) = 4`. The torsion
images are `(0,0) ↦ (−1, −d)`, `(d,0) ↦ (d, 2)` and `(−d,0) ↦ (−d, −2d)`. Their valuation patterns at
`p` are `(0,1)`, `(1,0)`, `(1,1)`, so they are distinct and nonzero, and they span the local image.
Writing a local class as (valuation, residue bit of the unit part), the image consists of
`ρ_p(a) = u_p[d_p/p] + v_p λ_p` and `ρ_p(b) = u_p μ_p + v_p[−d_p/p]`, with `d_p = d/p`. For
`a = (−1)^{a₀}2^{a₁}Π q^{u_q}` one has `ρ_p(a) = a₀λ_p + a₁μ_p + Σ_{q≠p} u_q[q/p]`. Equating and
using `[d_p/p] = Σ_{q≠p}[q/p]` gives
`Σ_{q≠p}[q/p](u_q + u_p) + λ_p v_p = a₀λ_p + a₁μ_p`, which is `E1_p`. The same computation for `b`
gives `μ_p u_p + Σ_{q≠p}[q/p](v_q + v_p) + λ_p v_p = b₀λ_p + b₁μ_p`, which is `E2_p`.

**Primes `p ∤ 2d`.** CORRECT (standard). Selmer classes are unramified outside `2d∞`, hence
represented by `a, b` supported on `−1, 2` and the primes of `d` (Silverman X.1.4); conversely, at a
prime of good reduction `p ∤ 2d` the local image is the unramified subgroup, so such classes
satisfy the local condition there. (Finding 3 concerns only the wording of this point.)

**Real place.** CORRECT. For `d > 0`, `E(ℝ)/2E(ℝ)` has order 2 and the image of `(0, 0)` is
`(−, −)`. So the condition is `a₀ = b₀`.

**Place 2, `c = 5`.** CORRECT. If `d/d'` is a 2-adic square, `(x, y) ↦ (t²x, t³y)` with `d = t²d'`
identifies `C_{d'}` and `C_d` over `ℚ₂` and preserves both Kummer coordinates, so the local image
depends on `d` only through `d mod 8` for odd `d > 0`. Take `d = 5`. `#E(ℚ₂)/2E(ℚ₂) = 4 · 2 = 8`.
The images contain `(5, 2)`, `(−1, −5) = (7, 3)` and `(1, 5)` from the point with `x = 1/4`:
`x³ − 25x = −399/64` and `−399 ≡ 1 (mod 16)`, so it is a 2-adic square, and
`(x, x − 5) = (1/4, −19/4) ≡ (1, 5)`. In bits `(v, ε, ω)` with `ε = (w−1)/2`, `ω = (w²−1)/8`: `5 = (0,0,1)`,
`2 = (1,0,0)`, `7 = (0,1,0)`, `3 = (0,1,1)`. The three images are `(0,0,1|1,0,0)`, `(0,1,0|0,1,1)`,
`(0,0,0|0,0,1)`. They are independent, and the general element `(0, y, x | x, y, y + z)` shows that
their span is `{a_v = 0, a_ε = b_ε, b_v = a_ω}`. The 2-adic class of
`a = (−1)^{a₀}2^{a₁}Π p^{u_p}` is `(a₁, a₀ + λ·u, μ·u)` because `ε(−1) = 1`, `ω(−1) = 0`,
`ε(p) = λ_p`, `ω(p) = μ_p`. With the real condition `a₀ = b₀` this gives `a₁ = 0`, `λ·u = λ·v`,
`b₁ = μ·u`: the row `(D)` for `c = 5`.

**Structure of the place-2 rows used by Lemmas 1 and 2.** CORRECT. In every class mod 8 the rows
involve `u, v` only through `λ·u, μ·u, λ·v, μ·v`, and they involve the configuration only through
`c(𝒞)`. Gluing preserves both (glue primes have `λ = μ = 0`; `λ`, `μ` are additive in products).

**Independent confirmation.** I wrote an exact 2-descent for `C_d` that does not use the system:
local images at odd `p | d` from the torsion points, at 2 from searched 2-adic points until the
dimension is 3, at `∞` from the torsion. It agrees with PARI's `ell2cover` on 30 random odd
squarefree `d` (1–5 primes below 400, all classes mod 8). My own implementation of `Σ(𝒞)` agrees
with it on 30 further random `d` (1–7 primes below 3000, 8, 9, 8, 5 curves with `d ≡ 1, 3, 5, 7`),
in dimension and in the membership of every signed odd divisor of `d` as a first coordinate. So
Proposition 0 also holds in the classes `c = 1, 3, 7` on this sample, although the proof never uses
them.

## 3. The gluing lemmas (§2.2)

A glue prime `r` has `c_r = 1`, so `λ_r = μ_r = 0` and `[x/r] = [r/x]` for all `x`.

**Lemma 1 (partner).** CORRECT. With `[r/y] = 1` for exactly one `y`, `E1_r` is
`[y/r](u_y + u_r) = u_y + u_r = 0` and `E2_r` is `v_y + v_r = 0`. The unknowns `u_r, v_r` occur
elsewhere only in `E1_y`, `E2_y`, through `[r/y](u_r + u_y)` and `[r/y](v_r + v_y)`, which vanish
once `E1_r`, `E2_r` hold. The rows `(D)` and `(R)` do not see `r`, and `c` is unchanged. So
forgetting `u_r, v_r` is a bijection onto the solutions of `Σ(𝒞 ∖ r)`, with inverse
`u_r = u_y`, `v_r = v_y`.

**Lemma 2 (gluing).** CORRECT, including the point the note flags (step 3). Put `X = G ∪ {g}`.

1. `E1_{r_ℓ}` is `[ℓ/r_ℓ](u_ℓ + u_{r_ℓ}) + [g/r_ℓ](u_g + u_{r_ℓ}) = u_ℓ + u_g = 0`; the `u_{r_ℓ}`
   cancel because `r_ℓ` has exactly two neighbours. Likewise `v_ℓ = v_g`.
2. At `y ∈ S'` no glue prime is linked to `y`, and the terms from `X` are
   `Σ_{x∈X}[x/y](u_x + u_y) = (Σ_{x∈X}[x/y])(u_g + u_y) = [g*/y](u_g + u_y)`. Same for `v`. So the
   rows at `S'` are those of `Σ(𝒞*)`.
3. `E1_ℓ` is
   `Σ_{y∈S'}[y/ℓ](u_y + u_ℓ) + Σ_{x∈X∖ℓ}[x/ℓ](u_x + u_ℓ) + (u_{r_ℓ} + u_ℓ) + λ_ℓ v_ℓ = a₀λ_ℓ + a₁μ_ℓ`
   (no other glue prime is linked to `ℓ`). With `u_X = u_g`, `v_X = v_g`, `a₁ = 0` this solves to
   (2.1). In `E1_g + Σ_ℓ E1_ℓ` the glue terms are `(u_{r_ℓ} + u_g) + (u_{r_ℓ} + u_ℓ) = u_g + u_ℓ`,
   which is `0` by step 1, whatever `u_{r_ℓ}` is; the terms between two elements of `X` are
   `[x'/x](u_{x'} + u_x) = 0` since `u_X` is constant, so no symmetry of the symbols inside `X` is
   used. What remains is `Σ_{y∈S'}(Σ_{x∈X}[y/x])(u_y + u_g) + (Σ_x λ_x)v_g = a₀Σλ_x + a₁Σμ_x`,
   which is `E1_{g*}`, because `λ` and `μ` are additive under products of classes, so
   `λ_{g*} = Σ_x λ_x` and `μ_{g*} = Σ_x μ_x`. For the `E2` rows, `Σ_x μ_x u_x = μ_{g*}u_g` as well,
   and `E2_ℓ` solves to (2.2), which I rederived term by term; `b₁` enters (2.2) but is a coordinate
   of the image.
4. `c(𝒞*) = c(𝒞)` and `λ·u = λ|_{S'}·u|_{S'} + λ_{g*}u_g` (glue primes contribute nothing); same
   for `μ·u`, `λ·v`, `μ·v`. So `(D)`, `(R)` agree.

Reciprocity in `𝒞*`: `[y/g*] + [g*/y] = Σ_{x∈X}([y/x] + [x/y]) = λ_y Σ_x λ_x = λ_yλ_{g*}`. Correct.
Injectivity and surjectivity are as stated: on the inverse side, `u_X = u_{g*}`, `u_R` from (2.1),
(2.2), and `E1_g` (resp. `E2_g`) then holds because `E1_g + Σ E1_ℓ` equals `E1_{g*}` identically
once `u_X` and `v_X` are constant.

A consequence used in finding 1: the symbols between two elements of `X` never enter any row of
`Σ(𝒞)` once `u_X`, `v_X` are constant, and they do not enter `𝒞*`. In step 5 of the theorem
`X = T ∪ {q₀}`, so the slot condition `[q₀/ℓ] = 0` (`ℓ ∈ T`) is not needed. My exhaustive test
(§6) confirms that dropping it changes nothing.

## 4. The base configuration (§2.3)

**Lemma 3.** CORRECT. With `c_{p*} = 7`, `c_{q₀} = 3`: `λ = (1, 1)`, `μ = (0, 1)`, `c = 21 ≡ 5`;
`[p*/q₀] = x + 1` by reciprocity. With `w = u_{p*} + u_{q₀}`, `(Ku)_{p*} = xw`, `(Ku)_{q₀} = (x+1)w`,
and the rows are exactly as displayed in the note. `E1` gives `v_{p*} = a₀ + xw`,
`v_{q₀} = a₀ + (x+1)w` (using `a₁ = 0`), so `v_{p*} + v_{q₀} = w`, which is the row `λ·v = λ·u`.
Then `E2_{p*}` reduces to `xw + a₀ + xw = a₀ = b₀`, and `E2_{q₀}` to
`u_{q₀} + (x+1)w + a₀ + (x+1)w = u_{q₀} + a₀ = b₀ + b₁`, both consequences of `(R)` and
`b₁ = μ·u = u_{q₀}`. Free: `a₀, u_{p*}, u_{q₀}`; dimension 3. For `u = (1, 0)`: `w = 1`,
`v_{p*} = a₀ + x`, `v_{q₀} = a₀ + x + 1`, `b₁ = 0`. This is `σ₀`, for either value of `x`.

The side claim that `{p*, q}` with one auxiliary prime gives dimension 3 and `±p* ∈ π₁` exactly for
`(c_{p*}, c_q) ∈ {(7, 3), (3, 7)}`, for either symbol, I confirmed by enumerating all 32 two-prime
configurations with my own system. It is not used in the proof.

## 5. The slots and the proof of DL (§2.4, §2.5)

### 5.1 Satisfiability of the slot conditions

CORRECT. Every condition the construction imposes is a condition on the **new** prime modulo an
**already fixed** prime: `[q₀/p]` and `[q₀/ℓ]` are residue conditions on `q₀` modulo `p ∈ P` and
`ℓ ∈ T`; `[r/y]` for a glue slot `r` is a residue condition on `r` modulo `y`. No condition is ever
imposed in the reverse direction on an earlier prime, so reciprocity creates no constraint: it only
determines the reverse symbols afterwards (`[y/r] = [r/y]` for `r ≡ 1 (mod 4)`,
`[y/q₀] = [q₀/y] + λ_y`), and Lemmas 1–2 and the theorem use these reverse symbols correctly.

- The moduli of one slot are `8` and pairwise distinct odd primes: `P ∩ T = ∅` by (θ2), `β` and `θ`
  are odd, and each slot is a new prime. Each odd condition "`r` is a nonzero square mod `y`" or
  "`r` is a non-square mod `y`" is a nonempty set of `(y−1)/2` invertible classes, including for
  `y = 3`. The class mod 8 (`3` or `1`) is invertible. By CRT the conditions define a nonempty union
  of invertible classes modulo `8Π y`, and Dirichlet gives infinitely many primes in it, so the
  slot can avoid all primes already used. Being a unit modulo each `y`, it is automatically prime
  to `βθ` and to the earlier slots.
- No slot condition depends on another slot's choice except through the list of moduli, so the
  sequential choice never gets stuck.
- Edge cases. If `θ = 1`, `T = ∅` and there are no `r_ℓ`. If `ω(β) = 1`, there are no `r_p` and
  `[q₀/p₀] = x`. If every prime of `β` (or of `θ`) is `≡ 3 (mod 4)`, nothing changes: the prescribed
  bits `1 + λ_p x` are just bits. If `3 ∤ β`, the construction allows `q₀ = 3`; this is harmless
  (Proposition 0 holds for every odd squarefree `d`, and `|n| ≥ 21` still). The primes `3, 7` of `β`
  that come from `m` are treated like any other prime of `β`.

The real-prime computation of §6 implements exactly these CRT and Dirichlet steps.

### 5.2 The theorem, step by step

**Reduction.** CORRECT. `C_n = C_{|n|}`, and the first Kummer coordinate is the class of `x`; so
`d₁ = |n|`, `d₂ = d₁θ` are odd, positive and squarefree (slots are distinct new primes, (θ2)).

**Step 1.** CORRECT. In `S₁ = P ∪ {q₀} ∪ R_P ∪ R_T`, each `r_ℓ` has nonzero symbol only at `q₀`:
zero at `P` and `R_P` by its own condition, zero at earlier `r_{ℓ'}` by its condition and at later
ones by theirs (reciprocity for `≡ 1 (mod 4)`), and its other partner `ℓ` is not in `S₁`. Lemma 1
removes the `r_ℓ` one at a time; each still has the single neighbour `q₀`.

**Step 2.** CORRECT. In `𝒞_Σ` on `P ∪ {q₀} ∪ R_P`, each `r_p` is linked exactly to `p` and `p₀`:
zero at `P ∖ {p, p₀}`, at `q₀` and at the other `r_{p'}` (earlier by its condition, later by
theirs). Lemma 2 with `g = p₀`, `G = P ∖ {p₀}`, `S' = {q₀}` gives `𝒞₀` on `{p*, q₀}` with
`c_{p*} = Π c_p = |β| mod 8 = 7` and `[q₀/p*] = Σ_{p∈P}[q₀/p] = x`; as a check, `[p*/q₀] =
Σ_p([q₀/p] + λ_p) = x + λ_{p*} = x + 1`, as Lemma 3 requires.

**Step 3.** CORRECT. Lemma 3 and Proposition 0 for `d₁` (`c = 5`).

**Step 4.** CORRECT. Lifting `σ₀` with `a₀ = s` through Lemma 2: `u_P = 1`, `u_{q₀} = 0`,
`v_P = s + x`, `v_{q₀} = s + x + 1`. By (2.1) with `S' = {q₀}`:
`u_{r_p} = [q₀/p](u_{q₀} + u_{p₀}) + u_{p₀} + λ_p(v_{p₀} + a₀) = [q₀/p] + 1 + λ_p x`, which is `0` by
the choice `[q₀/p] = 1 + λ_p x`. (`p₀` itself needs no condition; `[q₀/p₀]` only fixes the sum
`x`.) Through Lemma 1, `u_{r_ℓ} = u_{q₀} = 0`. So `u = 𝟏_P`, `a₀ = s`, `a₁ = 0`, and the first
coordinate is `(−1)^s|β| = β`.

**Step 5.** CORRECT, including the two uses of (θ4). Lemma 2 applies to `𝒞₂` with `g = q₀`,
`G = T`, `R = R_T`, `S' = P ∪ R_P`: each `r_ℓ` is linked exactly to `ℓ` and `q₀`. The glued vertex
has `c_{q₀*} = 3θ ≡ 3 (mod 8)` by (θ1), hence `λ_{q₀*} = μ_{q₀*} = 1` as for `q₀`. For `p ∈ P`:
`[q₀*/p] = [q₀/p] + Σ_ℓ[ℓ/p] = [q₀/p] + [θ/p] = [q₀/p]` by (θ4) and multiplicativity of the
Legendre symbol, and `[p/q₀*] = [p/q₀] + Σ_ℓ[p/ℓ]`, where `Σ_ℓ[p/ℓ] = Σ_ℓ([ℓ/p] + λ_pλ_ℓ) =
[θ/p] + λ_pλ_θ = 0` by (θ4) and `θ ≡ 1 (mod 4)`. (This is Jacobi reciprocity, written inside the
configuration.) For `r_p ∈ R_P`: `[r_p/ℓ] = 0` for all `ℓ ∈ T` by the condition on `r_p`, and
`[ℓ/r_p] = [r_p/ℓ]`, so `[r_p/q₀*] = [r_p/q₀] = 0` and likewise in reverse. So the glued
configuration is `𝒞_Σ` with `q₀*` in place of `q₀`, and `Σ(𝒞₂) ≅ Σ(𝒞_Σ) ≅ Σ(𝒞₁)`: dimension 3.

**Step 6.** CORRECT, including the sign. The class of step 4 in `Σ(𝒞_Σ)` has `u_P = 1`,
`u_{q₀} = 0`, `u_{R_P} = 0`, `a₀ = s` and `v_{q₀} = s + x + 1` (the value of `v_{g*}`, carried
over unchanged from `𝒞₀`). By (2.1) with `g = q₀`:
`u_{r_ℓ} = Σ_{p∈P}[p/ℓ](1 + 0) + Σ_{r_p}[r_p/ℓ](0 + 0) + 0 + λ_ℓ(s + x + 1 + s) = [|β|/ℓ] + λ_ℓ(x + 1)`.
(θ3) for the signed `β` gives `0 = [β/ℓ] = sλ_ℓ + [|β|/ℓ]`. So
`u_{r_ℓ} = λ_ℓ(s + x + 1) = 0` exactly because `x = s + 1`. Also `u_T = u_{q₀} = 0`. So the lifted
class has `u = 𝟏_P`, `a₀ = s`, `a₁ = 0`: first coordinate `β`.

The choice `x = s + 1` is free for the first curve (Lemma 3 holds for both values of `x`, and step 4
works for either) and forced only by step 6, as the note says. With `x = s`, step 6 gives
`u_{r_ℓ} = λ_ℓ`, so the lifted class acquires the factors `r_ℓ` for `ℓ ≡ 3 (mod 4)`; my negative
control (§6) shows that `β` then indeed leaves `π₁(Sel₂(C_{d₂}))` whenever `θ` has such a prime.

**Conclusion of the theorem.** CORRECT. Both curves have `dim Sel₂ = 3` and `β ∈ π₁`. Neither
certificate is of torsion type, since `n/β` and `nθ/β` are not `±1`.

## 6. Computations

All code is new and independent of the note's scripts. PARI (through `cypari2`) is used only to
compare dimensions, to factor integers and to test primality.

1. **Exact descent.** `sel2.py` computes `Sel₂(C_d)` for odd squarefree `d > 0` as the
   intersection of local conditions. At odd `p | d` the local image is the span of the torsion
   images; at 2 it is the span of the images of 2-adic points found by search, until the dimension
   reaches 3; at `∞` it comes from the torsion. It does not use the system of Proposition 0. Against
   PARI's `ell2cover` on 30 random `d` (1–5 primes below 400, all classes mod 8): 0 mismatches
   (`validate_sel2_pari.py`).
2. **Proposition 0.** `system.py` implements `Σ(𝒞)` (all four classes). Against `sel2.py` on 30
   random `d` (1–7 primes below 3000): dimensions and first-coordinate membership of every signed
   odd divisor of `d` agree, 0 mismatches (`validate_prop0.py`).
3. **The theorem on abstract data** (`abstract_dl.py`). The data are classes mod 8 for the primes
   of `β` (product `≡ 7`) and of `θ` (product `≡ 1`), a sign `s`, arbitrary symbols within `P` and
   within `T` (reciprocity imposed), and cross symbols `M_{pℓ} = [ℓ/p]` constrained exactly by
   (θ4) (row sums `0`) and (θ3) with reciprocity (column sums `(s + 1)λ_ℓ`). The slots are added
   with the symbols of §2.4, and both systems are solved.
   - Exhaustive over all such data with `|P| ≤ 3`, `|T| ≤ 3` (541,748 cases, including `θ = 1`,
     `ω(β) = 1`, and all-`λ = 1` classes): dimension 3 and the class `β`, with its sign, on both
     curves in every case (`out_abstract_exh.txt`).
   - 1,000 random cases with `|P|, |T| ≤ 10`: 0 failures (`out_abstract_more.txt`).
   - Negative control `x = s`: the first curve is always certified. The second loses `β` exactly
     when `θ` has a prime `≡ 3 (mod 4)`. In the exhaustive range `|P| + |T| ≤ 5` there are 10,568
     failures, and in each size class their number equals the number of data in which `θ` has such
     a prime (for instance `3/4` of the cases for `|T| = 3`, `1/2` for `|T| = 2`). In 300 random
     cases, 221 fail, all of that kind. This matches step 6, where `x = s` gives
     `u_{r_ℓ} = λ_ℓ`.
   - With the slot condition `[q₀/ℓ] = 0` replaced by random bits: 0 failures in the exhaustive
     range `|P| ≤ 3`, `|T| ≤ 2` (finding 1).
4. **End to end with actual primes** (`real_dl.py`). The construction of §2.4 uses CRT over the
   primes of `β` and `θ` with random admissible residues and searches the resulting progression for
   primes, testing the symbols at earlier slots. Both curves are certified with `sel2.py` (not with
   the system). Thirty runs `(B, m)`, one after another: 12 random admissible `B`; 6 with `θ = 1`
   (3 with `β > 0`, 3 with `β < 0`); 5 with every prime of `β` `≡ 3 (mod 4)`; 7 with a prescribed
   `θ` of 3–6 primes including primes `≡ 3 (mod 4)` (4 with `β > 0`, 3 with `β < 0`). Over the 30
   runs, `ω(β)` ranges over 1–8, `ω(θ)` over 0–6, 16 runs have `β < 0`, 20 have a prime `≡ 3 (mod
   4)` in `θ`, and 22 different multipliers occur, odd and even. Both curves have `dim Sel₂ = 3`
   and `β ∈ π₁` in **all 30 runs**, the number of slots is exactly `ω(β) + ω(θ)` (2–12), and the
   slots have at most 57 digits (`out_real_dl.txt`). Primality of the slots is BPSW, which is
   ample for a test.

## 7. The count (§2.6)

- **Count.** CORRECT. `n/β = q₀ · Π_{p≠p₀} r_p · Π_ℓ r_ℓ` has `1 + (ω(β) − 1) + ω(θ)` distinct
  primes, all new. My real-prime runs (§6) have exactly `ω(β) + ω(θ)` slots in every run.
- **Comparison with Proposition B.** Finding 2. In the setting of descent-alt Proposition B (an
  isotropic core `K` of `k` primes `≡ 1 (mod 21840)` with `K ⊆ supp β ⊆ K ∪ S₀`), `|β| ≡ 7 (mod 8)`
  forces a prime of `{3, 5, 7, 13}` into `β`, so `k + 1 ≤ ω(β) ≤ k + 4`, and the construction uses
  `ω(β)` auxiliary primes for the first curve: between one and four more than the bound. For
  general `β` there is no relation at all between `ω(β)` and the size of an isotropic core (which
  may be `0`). The note's phrase "within one of the lower bound" (introduction and §2.6) should be
  replaced by "of the same order as the lower bound in the core situation of Proposition B". This
  has no bearing on DL, which places no bound on the number of auxiliary primes; descent-alt §2(a)
  shows that none is needed.

## 8. The statement proved against the statement Route K needs

**What DL gives.** For every admissible `B`, an eligible `m` and `n = β · (slots)` such that
`C_{|n|}` and `C_{|n|θ}` have `dim Sel₂ = 3` and a Selmer class with first coordinate exactly `β`
(signed, `β = sqf(mB)`). That is the certificate of Selmer type of §1.2, for both curves, with the
same `m` defining `β` and `θ`.

**From certificate to point.** CORRECT, given the deep input. Since `C_d` has full rational
2-torsion, the corank lemma (manuscript line 1072) turns `dim Sel₂ = 3` into
`corank Sel_{2^∞} = 1`: the Kummer sequence gives `r + dim Ш[2] = 1`, and the alternating
Cassels–Tate pairing (Poonen–Stoll) makes `dim F[2]` even for the finite part `F` of `Ш[2^∞]`.
Kriz's Theorem 10.13 (`E = C_d`, `K = ℚ(i)`, `p = 2`; CM by `ℤ[i] = O_K` holds for every `d ≠ 0`)
gives `rank C_d(ℚ) = 1`. Kriz's construction assumes `f₀ ≥ 4`, where `f₀` is the odd part of `|d|`
here; for `d ∈ {d₁, d₂}` one has `f₀ = d ≥ 21`, so the LMFDB step of Kriz's proof is not reached
(finding 4). Then pc-audit RK9 applies: `C_d(ℚ)/2C_d(ℚ)` has dimension `2 + 1 = 3`, so it equals
`Sel₂`; the class `β` is the image of `P + 2Q` with `Q` of infinite order, a non-torsion point, and
for a non-torsion point the first Kummer coordinate is the class of `x`. Hence `x ∈ βℚ*²`
(`x ≠ 0`). Note that `|β| ≥ 7`, so `β ≢ ±1`, and `β ≢ ±d`; the class `β` cannot be a torsion class.

**From points to `Φ_C(B)`.** CORRECT. With `x + ℓ` in place of `x + 3ℓ`, the polynomial asks for
`b ∈ {0,1}⁶` (any signed divisor `m` of 2730 is realized), `A = mB`, `H = A(A − B²)`, a point
`(A, r₁)` on `C_e`, a point `(Az², zr₂)` on `C_{eH}` and `w = (eHz)^{-1}`, so `e, z, H ≠ 0`. Note
`H = mB²(m − B) ≡ m(m − B)`, so `sqf(H) = θ`, and `H ≠ 0` since `0 < B < 1/2`. Let `(βs², y₁)` lie on
`C_n` and `(βs'², y₂)` on `C_{nθ}`, and write `A = βt²`, `H = θh²`. Scaling by `(t/s)²` moves the
first point to `(A, y₁t³/s³)` on `C_e` with `e = nt²/s²`. Then `eH ≡ nθ`, and scaling the second
point by `t h/s` (so that the curve becomes `C_{nθ t²h²/s²} = C_{eH}`) gives a point with abscissa
`β s'² t²h²/s² = A z²`, `z = s'h/s ≠ 0`. All eleven witnesses are rational, and `w = (eHz)^{-1}`.
The sign of `n` is immaterial, since `C_n = C_{−n}`. This is the reformulation of rv-route-k
§4.2 in the direction that is used, and it needs exactly "a rational point with abscissa in `βℚ*²`
on `C_n` and on `C_{nθ}`, for one `m`", which is what the certificates give.

**Lean hypothesis.** The admissibility conditions of §1.1 coincide with the hypotheses of
`ZInQ.PoleCompleteness` (`IsSquare B.den`, `0 < B < 1/2`, `4 ≤ padicValRat p B` on `S₀`), and
`PoleSoluble` is the vanishing of `B` times a sum of squares, which for `B > 0` is the system above.
So DL, plus the passage from certificates to points, gives the `x + ℓ` version of PC for every
admissible `B`, with no restriction on `B` beyond those hypotheses.

**What DL does not settle.** The passage from certificate to point is the deep input (Kriz, an
unrefereed preprint, with the repair of its Theorem 10.8 noted in pc-audit RK1; or, for the
restricted 2-adic shape `|n| ≡ 5 (mod 8)`, `|β| ≡ 7 (mod 8)` that the construction always
produces, TYZ with Gross–Zagier if pc-audit RK6 holds). That is outside the scope of this report
and is UNCHECKED here.

## 9. Repairs and suggestions

No mathematical repair is required. Suggested edits to `slot-k.md`:

1. (Finding 1.) In §2.4 either drop the condition `[q₀/ℓ] = 0` for `ℓ ∈ T` or mark it as optional,
   and in §2.5 "What each slot does" replace "its symbols at `T` [are dictated] by the transfer to
   the second curve" by: "its symbols at `T` are irrelevant: they lie inside the glued set of
   step 5". Dropping it also removes `ω(θ)` conditions from the choice of `q₀`, which matters for a
   Lean formalization of L3.
2. (Finding 2.) Replace "within one of the lower bound of Proposition B" (introduction, §2.6) by a
   statement that is true in general, for instance: "in the core situation of Proposition B the
   first curve uses between `k + 1` and `k + 4` auxiliary primes, against the bound `k`".
3. (Finding 3.) In §2.1, state both directions: Selmer classes are unramified outside `2d∞`
   (Silverman X.1.4), hence supported on `−1, 2` and the primes of `d`; such classes satisfy the
   local conditions at good primes `p ∤ 2d` automatically.
4. (Finding 4.) In §1.2 and §4.1 cite Kriz's Theorem 10.13 rather than 10.17(2), as pc-audit RK1
   recommends, and record that Kriz's standing hypothesis `f₀ ≥ 4` holds because the odd part of
   `|d|` is `d ≥ 21` for both curves.
5. (Finding 5.) In §1.2 phrase the torsion certificate as: "`d ≡ β` or `d ≡ −β` modulo squares;
   then `(d, 0)` or `(−d, 0)` is a point of `C_d` with abscissa in `βℚ*²`". It is never used by the
   construction.
6. (Optional.) Step 5 can be written without Jacobi symbols: `Σ_ℓ[p/ℓ] = Σ_ℓ([ℓ/p] + λ_pλ_ℓ) =
   [θ/p] + λ_pλ_θ`, which is `0` by (θ4) and `θ ≡ 1 (mod 4)`. This is the form a Lean proof (L5)
   would use, since it needs only Legendre reciprocity prime by prime.
