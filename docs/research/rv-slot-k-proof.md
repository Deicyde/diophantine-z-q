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
signed divisors give `β` odd with `|β| ≡ 7 (mod 8)`: `v₂(m)` is forced, the 16 odd divisors of
2730 fall four into each class of `(ℤ/8)*`, and both signs are allowed. Every one of them satisfies (θ1)–(θ4), and the proof uses nothing else about `m`,
so the construction works for whichever eligible `m` is picked.

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
