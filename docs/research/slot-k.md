# The descent lemma of Route K: a slot construction

This note proves the descent lemma DL of `docs/research/descent-alt.md` §1.2, the step of Route K
(`docs/research/rs-pole.md` §4.1, `docs/research/rv-route-k.md` §4.4) that was still open. The
construction uses `ω(β) + ω(θ)` auxiliary primes:

- one prime `q₀ ≡ 3 (mod 8)`;
- `ω(β) − 1` primes `≡ 1 (mod 8)` that glue the primes of `β` into one "virtual prime";
- `ω(θ)` primes `≡ 1 (mod 8)` that glue the primes of `θ` onto `q₀`.

The proof is `𝔽₂`-linear algebra in the system of descent-alt Proposition 0. Two gluing operations
reduce both curves `C_n` and `C_{nθ}` to the same configuration of two primes, `p* ≡ 7` and
`q₀ ≡ 3 (mod 8)`. Its Selmer group has dimension 3 and contains the class `β`. The number of auxiliary
primes is within one of the lower bound of descent-alt Proposition B.

Every claim carries one of three marks.

- **VERIFIED**: proved in this note, checked against the cited text, or established by an exact
  computation. Scripts are in `scratch/slot-k/`.
- **STANDARD**: a published theorem, with a reference.
- **SPECULATIVE**: an idea or expectation that is not proved.

**Notation** (as in descent-alt).

- `C_d : y² = x³ − d²x`; Kummer map `P ↦ (x, x − d)` in `(ℚ*/ℚ*²)²`, with the usual replacements
  `(0,0) ↦ (−1, −d)`, `(d,0) ↦ (d, 2)`, `(−d,0) ↦ (−d, −2d)`.
- `sqf` is the signed squarefree part; `ω` counts distinct prime factors.
- For an odd prime `p` and `x` prime to `p`: `[x/p] ∈ 𝔽₂` is `0` if `x` is a square mod `p` and `1`
  otherwise. `λ_p = [−1/p]`, `μ_p = [2/p]`.
- For odd `y` and odd positive `N = Π ℓ`: `[y/N] = Σ_ℓ [y/ℓ]`, the bit of the Jacobi symbol.
- `π₁` is the projection of `Sel₂(C_d)` to the first Kummer coordinate.

## 1. The statement

### 1.1 Inputs, multipliers, `β` and `θ` (VERIFIED, descent-alt §1, §3.1)

- `B` is **admissible** if `B ∈ ℚ`, its reduced denominator is a square, `0 < B < 1/2`, and
  `v_p(B) ≥ 4` for `p ∈ S₀ = {2, 3, 5, 7, 13}`. This is the hypothesis of PC (manuscript
  Theorem 5.2, line 1001; Lean `ZInQ.PoleCompleteness`, `ZInQKernel/Hypotheses/Pole.lean`).
- For a signed divisor `m` of 2730 put `β = sqf(mB)` and `θ = sqf(m(m − B))`.
- For every admissible `B` and every `m` (descent-alt §3.1, manuscript lines 1027–1033):
  - (θ1) `θ > 0`, `θ ≡ 1 (mod 8)`, `gcd(θ, 2730) = 1`;
  - (θ2) `β` and `θ` have disjoint supports;
  - (θ3) `(β/ℓ) = 1` for every prime `ℓ | θ`;
  - (θ4) `(θ/p) = 1` for every odd prime `p | β`.

  *Proof* (recalled from descent-alt §3.1). Since `m(m − B) = m²(1 − B/m)` and `B/m = mB/m²`, there
  are rationals `c, t` with `θc² = 1 − βt²` and `βt² = B/m`. Every prime `p | m` lies in `S₀`, so
  `v_p(B/m) ≥ 3` there; for `p ∤ m`, `v_p(B/m) = v_p(B)` is even when negative (square denominator).
  - At 2 and at `3, 5, 7, 13`: `v_p(βt²) ≥ 3`, so `1 − βt²` is `≡ 1 (mod 8)` resp. a `p`-adic unit
    square. Hence `θ` is odd, `≡ 1 (mod 8)` and prime to 2730. Also `θ > 0`, since
    `|B/m| ≤ B < 1/2`. This is (θ1).
  - At an odd `p | β`: `v_p(βt²)` is odd, hence positive by the remark above. So `1 − βt²` is a
    `p`-adic unit square: `p ∤ θ` and `(θ/p) = 1`. This is (θ2) and (θ4).
  - At `ℓ | θ`: `v_ℓ(1 − βt²)` is odd. It cannot be that `v_ℓ(βt²) > 0` (then `1 − βt²` is a unit),
    nor that `v_ℓ(βt²) < 0` (then the valuation would be `v_ℓ(B)`, which is even). So `βt²` is an
    `ℓ`-adic unit with `βt² ≡ 1 (mod ℓ)`, and `(β/ℓ) = 1`. This is (θ3).

### 1.2 Certificates (VERIFIED, descent-alt Notation and §2(c); rv-route-k §4.3)

For squarefree `d` and the class `β`, a **certificate** for `C_d` is one of:

- (torsion) `d ≡ ±β` modulo squares; then `(β, 0)` or `(−β, 0)` lies on `C_d` up to the
  identification `C_d ≅ C_{−d}`; or
- (Selmer) `dim_{𝔽₂} Sel₂(C_d) = 3` and `β ∈ π₁(Sel₂(C_d))`.

In the Selmer case, Kriz's 2-converse (arXiv:2002.04767v5, Theorems 10.13 and 10.17(2)) together
with the corank lemma (`lem:corank`, manuscript line 1072; Poonen–Stoll, audit record A019) gives
`rank C_d(ℚ) = 1` and `Ш(C_d)[2] = 0`. Then `C_d(ℚ)/2C_d(ℚ) = Sel₂(C_d)`, so the class with first
coordinate `β` comes from a rational point (pc-audit RK9). This is the only use of a deep theorem;
pc-audit §2.2 states it as the hypothesis (R≥1) on the certified curves.

### 1.3 The lemma

> **DL.** For every admissible `B` there are a signed divisor `m` of 2730 and a squarefree `n` with
> `β | n` such that `C_n` and `C_{nθ}` both carry a certificate.

**Call sites** (VERIFIED, descent-alt §1.1 and §1.3). PC is applied in exactly two places:

- `ZInQ.Mult.slope_complete` (`Multiplication/Completeness/SlopeCompleteness.lean:187`;
  manuscript line 1751);
- `ZInQ.Assembly.test_complete` (`Assembly/Local/TestCompleteness.lean:104`; Lemma 11.2,
  manuscript line 6233).

Both feed PC an input `B = R₀s(q)²`, with `β` fixed by the instance and `θ` moved by the witness `q`.
At the test site `ω(β)` is unbounded. So the lemma is needed for all admissible `B`, with `θ`
arbitrary subject to (θ1)–(θ4). That is how it is proved below: the proof uses nothing about `θ`
beyond (θ1)–(θ4).

Under Route K, DL closes PC as follows (rv-route-k §4.2): if `C_n` and `C_{nθ}` each have a rational
point with abscissa in `βℚ*²`, then `Φ_C(B)` holds, hence `PoleSoluble B`. The certificates supply
these points through §1.2.

## 2. The construction and its proof

### 2.1 Configurations and the Selmer system (Proposition 0)

A **configuration** `𝒞` is a finite set `S` of symbols ("primes"), each with a class `c_x ∈ {1, 3, 5, 7}`
mod 8, and a matrix of bits `L_{xy} = [y/x]` (`x ≠ y`) satisfying reciprocity:
`[x/y] + [y/x] = λ_xλ_y`, where `λ_x = [c_x ≡ 3 (mod 4)]` and `μ_x = [c_x ≡ 3, 5 (mod 8)]`.
Put `c(𝒞) = Π c_x mod 8`. An odd squarefree `d > 0` with prime set `S` defines a configuration by its
Legendre symbols; reciprocity holds by the quadratic reciprocity law (STANDARD).

The **Selmer system** `Σ(𝒞)` has unknowns `a₀, a₁, b₀, b₁ ∈ 𝔽₂` and `u, v ∈ 𝔽₂^S`. Write `K` for the
matrix `(Ku)_x = Σ_{y ≠ x} [y/x](u_y + u_x)` (Monsky's matrix; the manuscript's `K` at line 1040). The
equations are:

```
(E1_x)  (Ku)_x + λ_x v_x = a₀λ_x + a₁μ_x                     for every x ∈ S
(E2_x)  μ_x u_x + (Kv)_x + λ_x v_x = b₀λ_x + b₁μ_x          for every x ∈ S
(R)     a₀ = b₀
(D)     the two 2-adic rows for c(𝒞):
          c = 1: a₁ = 0, μ·u = 0, λ·v = λ·u        c = 3: a₁ = 0, b₀ = λ·v, b₁ = μ·u
          c = 5: a₁ = 0, b₁ = μ·u, λ·v = λ·u       c = 7: a₁ = 0, μ·u = 0, b₀ = λ·v
```

A solution corresponds to the pair of classes `a = (−1)^{a₀}2^{a₁}Π x^{u_x}`,
`b = (−1)^{b₀}2^{b₁}Π x^{v_x}`.

**Proposition 0** (descent-alt §4.1, VERIFIED there). If `𝒞` is the configuration of an odd squarefree
`d > 0`, then `(a, b) ↦ solution` identifies `Sel₂(C_d)` with the solution space of `Σ(𝒞)`.

- The rows at an odd `p | d` are the local conditions at `p`. The local image is spanned by the
  torsion images `(d, 2)` and `(−1, −d)`. For each of the four valuation patterns `(u_p, v_p)` of
  `(a, b)` at `p`, `E1_p` and `E2_p` prescribe the residue symbols of the unit parts of `a` and `b`:
  these symbols are `u_p[d_p/p] + v_p[−1/p]` for `a` and `u_p[2/p] + v_p[−d_p/p]` for `b`,
  where `d_p = d/p`.
- descent-alt checked the system against an independent exact descent (`sel2cong.py`, itself
  checked against PARI in rv-route-k) on 600 curves with 0 mismatches.

**What the proof uses from Proposition 0** (VERIFIED here independently of descent-alt's table).

- *Odd places and the real place*: as above, proved by hand in descent-alt §4.1. Classes are
  automatically unramified outside `2d∞`, since they are supported on `−1, 2` and the primes of `d`
  (Silverman, *The Arithmetic of Elliptic Curves*, X.1.4; STANDARD).
- *Structure of the place-2 rows.* Write the class of a 2-adic unit `w` as `(ε, ω)` with
  `ε = (w − 1)/2` and `ω = (w² − 1)/8` mod 2. For `a = (−1)^{a₀}2^{a₁}Π p^{u_p}` the 2-adic class is
  `(v, ε, ω) = (a₁, a₀ + λ·u, μ·u)`, because `ε(−1) = 1`, `ω(−1) = 0`, `ε(p) = λ_p` and `ω(p) = μ_p`.
  Likewise for `b`, with `(b₁, b₀ + λ·v, μ·v)`. The local image at 2 depends only on the class of `d` in
  `ℚ₂*/ℚ₂*²`, which is `c(𝒞)` for odd `d > 0`, since `C_d ≅ C_{d'}` over `ℚ₂` when `d/d'` is a 2-adic
  square. So the rows `(D)` depend on `𝒞` only through `c(𝒞)`, and on `u, v` only through
  `λ·u, μ·u, λ·v, μ·v`. This is all that Lemmas 1 and 2 use.
- *The rows for `c = 5`*, used in Lemma 3. Over `ℚ₂`, `C_d ≅ C_5`. The image of
  `C_5(ℚ₂)/2C_5(ℚ₂)` (dimension 3, since `#E(ℚ₂)/2E(ℚ₂) = 4 · 2`) contains the torsion images
  `(5, 2)` and `(−1, −5) ≡ (7, 3)`, and the image `(1, 5)` of the point with `x = 1/4`. Indeed
  `x − 5 = −19/4` and `x + 5 = 21/4` both have class 5, so `x(x − 5)(x + 5)` is a square in `ℚ₂`.
  In bits `(v, ε, ω | v, ε, ω)` the three generators are `(0,0,1 | 1,0,0)`, `(0,1,0 | 0,1,1)` and
  `(0,0,0 | 0,0,1)`. They span the space cut out by `a_v = 0`, `a_ε = b_ε`, `b_v = a_ω`. With `(R)`
  these are exactly `a₁ = 0`, `λ·u = λ·v`, `b₁ = μ·u`, the row of `(D)` for `c = 5`.

The torsion classes `(1,1)`, `(−1,−d)`, `(d,2)`, `(−d,−2d)` have `u ∈ {0, 𝟏_S}`. A class with
first coordinate `±β` therefore has `u = 𝟏_{supp β}` or, after adding `(d, 2)`, `u = 𝟏_{S ∖ supp β}`.

The Selmer system makes sense for any configuration, whether or not a squarefree number realizes it.
Configurations that are not realized ("virtual" ones) appear below as intermediate steps only. The
final statements concern actual curves.

### 2.2 Two gluing lemmas (VERIFIED, proved here)

In both lemmas `𝒞` is a configuration on `S`, and a **glue prime** is a symbol `r` with `c_r = 1`
(so `λ_r = μ_r = 0` and `[r/x] = [x/r]` for all `x`).

**Lemma 1 (partner).** Let `r ∈ S` be a glue prime with `[r/y] = 1` for exactly one `y ∈ S`. Then
the map that forgets `u_r, v_r` is an isomorphism from the solutions of `Σ(𝒞)` onto those of
`Σ(𝒞 ∖ r)`. The inverse sets `u_r = u_y`, `v_r = v_y`.

*Proof.* `E1_r` reads `[y/r](u_y + u_r) = u_y + u_r = 0`, and `E2_r` reads `v_y + v_r = 0`. The only
other rows that contain `u_r` or `v_r` are `E1_y`, `E2_y`, through the terms `u_r + u_y` and
`v_r + v_y`, which vanish once `E1_r`, `E2_r` hold. The diagonal of `K` is built into the terms
`u_r + u_y`, so no other entry changes. `c(𝒞 ∖ r) = c(𝒞)` because `c_r = 1`, and `r` contributes
nothing to `λ·u`, `μ·u`, `λ·v`, `μ·v`. ∎

**Lemma 2 (gluing).** Let `S = S' ⊔ {g} ⊔ G ⊔ R`, where `R = {r_ℓ : ℓ ∈ G}` consists of glue primes
with

```
[r_ℓ/ℓ] = [r_ℓ/g] = 1,    [r_ℓ/x] = 0 for every other x ∈ S.
```

Let `𝒞*` be the configuration on `S' ⊔ {g*}` that agrees with `𝒞` on `S'` and has

```
c_{g*} = c_g Π_{ℓ∈G} c_ℓ,    [y/g*] = Σ_{x ∈ G∪{g}} [y/x],    [g*/y] = Σ_{x ∈ G∪{g}} [x/y]    (y ∈ S').
```

(Reciprocity holds for `𝒞*`, because `λ_{g*} = Σ_x λ_x`.) Then the map
`Φ : (a, b, u, v) ↦ (a, b, u|_{S'}, u_g ↦ u_{g*}, v|_{S'}, v_g ↦ v_{g*})` is an isomorphism from the
solutions of `Σ(𝒞)` onto those of `Σ(𝒞*)`. In the inverse, `u_ℓ = u_g`, `v_ℓ = v_g` for `ℓ ∈ G`, and

```
u_{r_ℓ} = Σ_{y∈S'} [y/ℓ](u_y + u_g) + u_g + λ_ℓ(v_g + a₀),                                    (2.1)
```

with `a₁ = 0`, which `(D)` forces. Likewise, from `E2_ℓ`,

```
v_{r_ℓ} = Σ_{y∈S'} [y/ℓ](v_y + v_g) + v_g + μ_ℓu_g + λ_ℓ(v_g + b₀) + b₁μ_ℓ.                    (2.2)
```

Here `b₁` need not vanish, but it is carried along by `Φ`, so (2.2) is a function of the image.

*Proof.* Let `X = G ∪ {g}`.

1. *The glue rows force the gluing.* For `ℓ ∈ G`, `E1_{r_ℓ}` reads `(u_ℓ + u_{r_ℓ}) + (u_g + u_{r_ℓ}) = 0`,
   that is `u_ℓ = u_g`. Likewise `E2_{r_ℓ}` gives `v_ℓ = v_g`.
2. *Rows at `y ∈ S'`.* No `r_ℓ` is linked to `y`. The terms of `(Ku)_y` from `X` are
   `Σ_{x∈X} [x/y](u_x + u_y) = [g*/y](u_g + u_y)`, since all `u_x` equal `u_g`. So `E1_y` and
   `E2_y` coincide with the rows of `Σ(𝒞*)` at `y`.
3. *Rows at `X`.* The unknown `u_{r_ℓ}` occurs only in `E1_{r_ℓ}` (where it cancels), in `E1_ℓ` and in
   `E1_g`, through the terms `u_{r_ℓ} + u_ℓ` and `u_{r_ℓ} + u_g`. So `E1_ℓ` determines `u_{r_ℓ}`,
   which gives (2.1). The sum `E1_g + Σ_{ℓ∈G} E1_ℓ` does not contain any `u_{r_ℓ}`. In it, the terms
   between two elements of `X` are `[x'/x](u_g + u_g) = 0`. What remains is
   `Σ_{y∈S'} [y/g*](u_y + u_g) + λ_{g*} v_g = a₀λ_{g*} + a₁μ_{g*}`, which is the row `E1_{g*}` of `Σ(𝒞*)`.
   The same computation applies to the `E2` rows, with `Σ_x μ_x u_x = μ_{g*}u_g`.
4. *Places 2 and ∞.* `c(𝒞*) = c(𝒞)`, because the glue primes are `≡ 1 (mod 8)`. Also
   `λ·u = λ|_{S'}·u|_{S'} + λ_{g*}u_g`, and likewise for `μ·u`, `λ·v` and `μ·v`. So `(D)` and `(R)`
   are the same on both sides.

So `Φ` maps solutions to solutions. It is injective: if the image is 0, then `u_X = v_X = 0` by step 1,
and (2.1), (2.2) give `u_R = v_R = 0`. It is surjective: given a solution of `Σ(𝒞*)`, set
`u_X = u_{g*}`, `v_X = v_{g*}` and define `u_R`, `v_R` by `E1_ℓ`, `E2_ℓ`. The rows at `r_ℓ`, `ℓ` and `S'`
then hold by steps 1–3, `E1_g` holds because `E1_g + Σ E1_ℓ` is `E1_{g*}`, and step 4 handles the rest. ∎

`t1_transfer.py` tests the use of Lemma 2 made in §2.5 (gluing the primes of `θ` onto an auxiliary
prime) on 200 random configurations of actual primes. The Selmer dimensions of the two curves agree
in all 200 cases.

### 2.3 The base configuration (VERIFIED, proved here)

**Lemma 3.** Let `𝒞₀` be a configuration on `{p*, q₀}` with `c_{p*} = 7`, `c_{q₀} = 3` and
`x = [q₀/p*]` (so `[p*/q₀] = x + 1`). Then the solution space of `Σ(𝒞₀)` has dimension 3. It contains,
for each `a₀ ∈ 𝔽₂`, the solution

```
σ₀ :  u = (u_{p*}, u_{q₀}) = (1, 0),   v_{p*} = a₀ + x,   v_{q₀} = a₀ + x + 1,   a₁ = 0,  b₀ = a₀,  b₁ = 0.
```

*Proof.* `λ = (1, 1)`, `μ = (0, 1)`, `c(𝒞₀) = 21 ≡ 5`. Put `w = u_{p*} + u_{q₀}`. Then
`(Ku)_{p*} = xw` and `(Ku)_{q₀} = (x + 1)w`. The rows are:

- `E1_{p*}`: `xw + v_{p*} = a₀`; `E1_{q₀}`: `(x + 1)w + v_{q₀} = a₀`;
- `E2_{p*}`: `x(v_{p*} + v_{q₀}) + v_{p*} = b₀`; `E2_{q₀}`: `u_{q₀} + (x + 1)(v_{p*} + v_{q₀}) + v_{q₀} = b₀ + b₁`;
- `(R)`: `a₀ = b₀`; `(D)` for `c = 5`: `a₁ = 0`, `b₁ = u_{q₀}`, `v_{p*} + v_{q₀} = w`.

The `E1` rows give `v_{p*} = a₀ + xw` and `v_{q₀} = a₀ + (x + 1)w`, so `v_{p*} + v_{q₀} = w`, and the last
row of `(D)` holds. Substituting, `E2_{p*}` becomes `a₀ = b₀` and `E2_{q₀}` becomes `u_{q₀} + a₀ = b₀ + b₁`.
Both follow from `(R)` and `b₁ = u_{q₀}`. So `a₀, u_{p*}, u_{q₀}` are free and the other unknowns are
determined: the dimension is 3. Taking `u = (1, 0)`, `w = 1`, gives `σ₀`. ∎

The exhaustive search `t2_template.py` confirms Lemma 3 and shows that it is the smallest possible
base. With one auxiliary prime `q`, a configuration `{p*, q}` has dimension 3 and `p* ∈ π₁` exactly
when `(c_{p*}, c_q) ∈ {(7, 3), (3, 7)}`, for either value of the symbol. For `c_{p*} ∈ {1, 5}` at
least two auxiliary primes are needed.

For actual primes `p ≡ 7`, `q ≡ 3 (mod 8)`, Lemma 3 with Proposition 0 says that `Sel₂(C_{pq})` has
dimension 3 and contains a class with first coordinate `p`.

### 2.4 The slots

Let `B` be admissible.

**Step 0 (multiplier).** Choose a signed divisor `m` of 2730 such that `β = sqf(mB)` is odd and
`|β| ≡ 7 (mod 8)`. Such an `m` exists (VERIFIED):

- the parity of `v₂(β)` is `v₂(B) + v₂(m)` mod 2, so `v₂(m) ≡ v₂(B)` makes `β` odd;
- then `|β| ≡ |m_odd| · b (mod 8)`, where `b` is the odd squarefree kernel of `|B|`, because odd squares
  are `≡ 1 (mod 8)`;
- the odd parts `1, 3, 5, 7, 13, 15, 21, 35, …` of the divisors of 2730 cover all four classes mod 8
  (for instance `1, 3, 5, 7`);
- the sign of `m` is free and does not change `|β|`.

Let `P` be the set of primes of `β`, so `|β| = Π_{p∈P} p` and `P ≠ ∅` (since `|β| ≡ 7`), and let `T`
be the set of primes of `θ` (possibly empty). Fix `p₀ ∈ P`. Put `s = [β < 0]` and `x = s + 1 ∈ 𝔽₂`.

**Slot `q₀`.** A prime `q₀ ∤ 2βθ` with

```
q₀ ≡ 3 (mod 8),
[q₀/p] = 1 + λ_p x                      for p ∈ P ∖ {p₀},
[q₀/p₀] = x + Σ_{p ∈ P∖{p₀}} (1 + λ_p x),
[q₀/ℓ] = 0                              for ℓ ∈ T.
```

By construction `Σ_{p∈P} [q₀/p] = x`.

**Slots `r_p`, for `p ∈ P ∖ {p₀}`** (chosen one after the other). A prime `r_p` with

```
r_p ≡ 1 (mod 8),    [r_p/p] = [r_p/p₀] = 1,
[r_p/y] = 0  for y ∈ (P ∖ {p, p₀}) ∪ T ∪ {q₀} ∪ {earlier r_{p'}}.
```

**Slots `r_ℓ`, for `ℓ ∈ T`** (chosen one after the other). A prime `r_ℓ` with

```
r_ℓ ≡ 1 (mod 8),    [r_ℓ/ℓ] = [r_ℓ/q₀] = 1,
[r_ℓ/y] = 0  for y ∈ P ∪ (T ∖ {ℓ}) ∪ {all r_p} ∪ {earlier r_{ℓ'}}.
```

Finally

```
n = β · q₀ · Π_{p ∈ P∖{p₀}} r_p · Π_{ℓ ∈ T} r_ℓ,      ω(n/β) = ω(β) + ω(θ).
```

**Existence of the slots** (VERIFIED). Each slot is subject to one condition modulo 8 and one condition
modulo each of finitely many distinct odd primes `y` already fixed: "`r` is a nonzero square mod `y`"
or "`r` is a non-square mod `y`". Each such condition is a nonempty union of invertible classes mod
`y`, since an odd prime has `(y − 1)/2 ≥ 1` squares and as many non-squares. By the Chinese remainder
theorem the conditions together define a nonempty union of invertible classes modulo
`8 Π y`. By Dirichlet's theorem on primes in arithmetic progressions (STANDARD; audit record A057)
each class contains infinitely many primes, so the slot can be chosen outside the finite set of
primes already used. The conditions never conflict, because each refers to a different modulus.

The conditions fix the symbols `[slot/y]`. The reverse symbols `[y/slot]` are then fixed by quadratic
reciprocity: `[y/r] = [r/y]` for the glue slots `r ≡ 1 (mod 4)`, and
`[y/q₀] = [q₀/y] + λ_y` for `q₀ ≡ 3 (mod 4)`. Lemmas 1 and 2 are stated with this convention.

### 2.5 The proof of DL (VERIFIED)

**Theorem.** With the choices of §2.4, `C_n` and `C_{nθ}` both have `dim_{𝔽₂} Sel₂ = 3`, and `β` is a
first coordinate of both Selmer groups. So both curves carry a certificate of Selmer type, and DL
holds with `ω(β) + ω(θ)` auxiliary primes.

*Proof.* `C_d` depends only on `d²`, and the first Kummer coordinate is the class of `x`. So we may
replace `n` by `d₁ = |n|` and `nθ` by `d₂ = d₁θ`. Both are odd, positive and squarefree: the slots are
distinct primes outside `2βθ`, and `β`, `θ` are coprime by (θ2). Let `𝒞₁`, `𝒞₂` be their
configurations, on `S₁ = P ∪ {q₀} ∪ R_P ∪ R_T` and `S₂ = S₁ ∪ T`. By Proposition 0 it suffices to work
with `Σ(𝒞₁)` and `Σ(𝒞₂)`.

*The first curve.*

1. Each `r_ℓ ∈ R_T` has exactly one nonzero symbol inside `S₁`, namely at `q₀` (its other one is at
   `ℓ ∉ S₁`). Removing them one at a time by Lemma 1 identifies `Σ(𝒞₁)` with `Σ(𝒞_Σ)`, where `𝒞_Σ`
   is the configuration on `P ∪ {q₀} ∪ R_P`. The inverse sets `u_{r_ℓ} = u_{q₀}`, `v_{r_ℓ} = v_{q₀}`.
2. Lemma 2 applies to `𝒞_Σ` with `g = p₀`, `G = P ∖ {p₀}`, `R = R_P` and `S' = {q₀}`: the slots `r_p`
   have exactly the required symbols. The glued configuration `𝒞₀` lives on `{p*, q₀}`, with
   `c_{p*} = |β| mod 8 = 7`, `c_{q₀} = 3` and `[q₀/p*] = Σ_{p∈P} [q₀/p] = x`.
3. By Lemma 3, `Σ(𝒞₀)` has dimension 3. Hence `dim Sel₂(C_{d₁}) = 3`.
4. Lift the solution `σ₀` of Lemma 3 with `a₀ = s`. Through Lemma 2: `u_P = 𝟏_P`, `u_{q₀} = 0`,
   `v_{q₀} = s + x + 1`, `v_{p₀} = s + x`, and by (2.1), for `p ∈ P ∖ {p₀}`,

   ```
   u_{r_p} = [q₀/p](0 + 1) + 1 + λ_p(v_{p₀} + a₀) = [q₀/p] + 1 + λ_p x = 0
   ```

   by the choice of `[q₀/p]`. Through Lemma 1: `u_{r_ℓ} = u_{q₀} = 0`. So `Sel₂(C_{d₁})` contains a
   class with `u = 𝟏_P`, `a₀ = s`, `a₁ = 0`. Its first coordinate is `(−1)^s|β| = β`.

*The second curve.*

5. Lemma 2 applies to `𝒞₂` with `g = q₀`, `G = T`, `R = R_T` and `S' = P ∪ R_P`. The glued vertex
   `q₀*` has class `3·θ ≡ 3 (mod 8)` by (θ1). Its symbols with `y ∈ S'` are as follows.
   - For `p ∈ P`: `[p/q₀*] = [p/q₀] + [p/θ]` and `[q₀*/p] = [q₀/p] + [θ/p]`. By (θ4), `(θ/p) = 1`.
     By the reciprocity law for Jacobi symbols (STANDARD), since `θ ≡ 1 (mod 4)` and `θ > 0`,
     `(p/θ) = (θ/p) = 1`. So both symbols are those of `q₀`.
   - For `r_p ∈ R_P`: all symbols between `r_p` and `T` vanish by construction.

   So the glued configuration is `𝒞_Σ` itself, with `q₀*` in place of `q₀`. By step 1,
   `Σ(𝒞₂) ≅ Σ(𝒞_Σ) ≅ Σ(𝒞₁)`, and `dim Sel₂(C_{d₂}) = 3`.
6. Lift the class of step 4 (in `Σ(𝒞_Σ)`: `u_P = 𝟏_P`, `u_{q₀} = 0`, `u_{R_P} = 0`, `a₀ = s`,
   `v_{q₀} = s + x + 1`) through Lemma 2. Then `u_T = u_{q₀} = 0` and, by (2.1), for `ℓ ∈ T`,

   ```
   u_{r_ℓ} = Σ_{p∈P} [p/ℓ] + λ_ℓ(v_{q₀} + a₀) = [|β|/ℓ] + λ_ℓ(x + 1).
   ```

   By (θ3), `[β/ℓ] = 0`, that is `[|β|/ℓ] = sλ_ℓ`. So `u_{r_ℓ} = λ_ℓ(s + x + 1) = 0`, because
   `x = s + 1`. The lifted class has `u = 𝟏_P`, `a₀ = s`, `a₁ = 0`: its first coordinate is `β`.

Both curves therefore carry a certificate of Selmer type. It is never of torsion type, since
`n/β` and `nθ/β` are not `±1`. ∎

**What each slot does.**

- `q₀` is the symmetry-breaking slot that Proposition C requires (a prime `≡ 3 (mod 4)`). Together
  with the glued prime `p*` it forms the two-prime base of Lemma 3. Its symbols at `P ∖ {p₀}` are
  dictated by the lifting condition `u_{r_p} = 0`, and its symbols at `T` by the transfer to the
  second curve.
- The `r_p` reduce the primes of `β` to one virtual prime of class 7. The Selmer group does not
  change (Lemma 2), and the class `β` survives because of the choice of `[q₀/p]`.
- The `r_ℓ` hang the primes of `θ` on `q₀`, so that the second curve has the same Selmer group as the
  first. The class `β` survives because of (θ3) and the choice `x = s + 1`. This is where the sign of
  `β` enters.

**The invariant.** The construction is not an iterative descent; each step is an exact isomorphism.
The invariant is the number of symbols of the configuration outside the base `{p*, q₀}`:

- for `C_{d₁}` it is `2(ω(β) − 1) + ω(θ)`, and for `C_{d₂}` it is `2(ω(β) − 1) + 2ω(θ)`;
- each application of Lemma 1 lowers it by one, and Lemma 2 lowers it by `2|G|`;
- the Selmer group (and the lift of the class `β`) is unchanged at each step, and the process ends
  at the base, where Lemma 3 computes everything.

This is different from greedy one-prime descent (descent-alt §4.7), which adds the prime that most
lowers a potential and stalls on plateaus. Here the slots are prescribed in advance. The potential
need not decrease at every step, and it does not have to: the proof computes the end result
directly.

### 2.6 How many auxiliary primes, and comparison with the lower bound

- **Count.** `ω(n/β) = ω(β) + ω(θ)`: one `q₀ ≡ 3 (mod 8)`, `ω(β) − 1` primes `≡ 1 (mod 8)` for `β`,
  and `ω(θ)` primes `≡ 1 (mod 8)` for `θ` (VERIFIED, §2.4).
- **Proposition B** (descent-alt §4.4). If `β` has an isotropic core of size `k`, every certificate
  needs at least `k` auxiliary odd primes visible to the core. Here `|β| ≡ 7 (mod 8)` and core primes
  are `≡ 1 (mod 8)`, so `ω(β) ≥ k + 1`. For the first curve the construction uses
  `ω(β) ≥ k + 1` auxiliary primes (`q₀` and the `r_p`; the `r_ℓ` do not count, being partners).
  This is within one of the bound.
- **The `θ`-slots are a device of the proof.** They are not forced: the random searches of
  rv-route-k and descent-alt found certificates with 2–4 auxiliary primes in total on most inputs.
  Whether `ω(β) + O(1)` slots always suffice is open (§5).
- **The manuscript.** The proof for `E_ℓ` (lines 1044–1061) uses `d − 1` slots of type `(0,0)` and
  one slot `q₀` of type `(1,1)`, where `d = ω(β)`. That is the same shape as `R_P ∪ {q₀}` here. The
  manuscript then asserts that "adding the support of `θ` preserves this block" (line 1050). The
  slots `r_ℓ` and Lemma 2 make the corresponding step explicit for `C_d`.
- **The K-TYZ-β rule** (pc-audit §4.2). `|n| ≡ 7 · 3 ≡ 5 (mod 8)`, `β` is odd and `|β| ≡ 3 (mod 4)`.
  This is the 2-adic rule under which pc-audit expects TYZ's row 5b to certify both curves. That
  expectation rests on pc-audit RK6, which this note does not check (SPECULATIVE here).

## 3. Validation

### 3.1 The algorithm

`scratch/slot-k/slotk.py` implements §2.4 with actual primes; `run_dl.py` and `run_families.py` are
the drivers.

1. Factor `β` and `θ` (PARI) for every signed divisor `m` with `β` odd and `|β| ≡ 7 (mod 8)`.
2. Choose `q₀`, then the `r_p`, then the `r_ℓ`, as in §2.4. The conditions modulo 8 and modulo the
   primes of `βθ` are imposed by the Chinese remainder theorem. The conditions modulo earlier slots
   are imposed by searching the resulting progression and testing Jacobi symbols. (Imposing them by
   CRT as well would double the size of the slots at each step.)
3. Certify `C_n` and `C_{nθ}` with the exact 2-descent `scratch/rv-route-k/sel2cong.py`. It computes
   the local images at odd primes from the torsion points, at 2 from explicit 2-adic points, and was
   checked against PARI in rv-route-k. It is independent of Proposition 0 and of §2. The output is
   `selmer3` when `dim Sel₂ = 3` and `β ∈ π₁`.

The slots in the tests have at most 89 digits. The exact descent only needs Legendre symbols, so
their size does not matter.

### 3.2 Results (VERIFIED, exact descent)

Each line is one input family. A *run* is one input with one multiplier; every multiplier with `β`
odd and `|β| ≡ 7 (mod 8)` was run (8 per input), except for `random30` and `smooth`, which use one.

| Family | Source | Inputs | Runs | Both curves certified | `ω(β)` | `ω(θ)` | Slots |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `random30` | 30 random admissible `B` (generator of descent-alt `common.py`, seed 2026) | 30 | 30 | 30 | 2–6 | 2–5 | 4–10 |
| `allm` | 5 random admissible `B`, all eligible multipliers (seed 77) | 5 | 40 | 40 | 1–6 | 1–6 | 4–11 |
| `B123` | the three inputs of descent-alt §4.3 with no certifying multiplier for `n = β` | 3 | 24 | 24 | 7–11 | 1–7 | 9–17 |
| `e11` | the two core-6 inputs of `e11_core_check.py` (`out_e11_core6.txt`; #0 is `B₃`) | 2 | 16 | 16 | 7–9 | 1–7 | 9–15 |
| `core3` | 3 inputs with an isotropic core of size 3 (as in `e10_core_instance.py`) | 3 | 24 | 24 | 4–6 | 1–7 | 6–11 |
| `core6` | 3 inputs with an isotropic core of size 6 (as in `e11_core_check.py`) | 3 | 24 | 24 | 7–9 | 2–8 | 10–15 |
| `stall` | the 6 inputs on which greedy descent stalls (below) | 6 | 48 | 48 | 2–6 | 1–6 | 3–11 |
| `smooth` | 10 smooth-`θ` inputs of rv-route-k (`gen_smooththeta`, `m = 1`) | 10 | 10 | 10 | 3–6 | 4–9 | 7–15 |
| **total** | | **62** | **216** | **216** | | | |

In every run the number of slots is exactly `ω(β) + ω(θ)`, as §2.6 states.

Notes on the families.

- *Greedy stalls.* `out_e8_greedy_random30.txt` does not record the inputs. The seed and size bound
  (7 and 9) were recovered by `find_seed_e8.py` from its first line, and `e8_replay.py` reran the
  greedy descent of descent-alt §4.7 printing `B`. The replay agrees on the first inputs, then
  diverges because of random tie-breaking, but it is the same algorithm. It stalls on six inputs
  (#8, #18, #19, #20, #23, #28 of `out_e8_replay.txt`). On #8 even the random fallback search of
  e8 found nothing.
- *Smooth `θ`.* The family is designed for `m = 1`. Inputs were drawn until `m = 1` gives `β` odd
  with `|β| ≡ 7 (mod 8)`, so that the construction runs on the smooth `θ` itself (up to 9 primes
  below 100).
- *Core instances.* The core primes are `≡ 1 (mod 21840)` and pairwise residues. Since
  `|β| ≡ 7 (mod 8)`, `β` has at least one prime outside the core, so `ω(β) ≥ k + 1`, in line with
  Proposition B.

### 3.3 Tests of the proof itself

- **Abstract configurations** (`t3_symbolic.py`, VERIFIED with the system of Proposition 0 as
  implemented in descent-alt `symsel.py`). Random data satisfying only (θ1)–(θ4): classes mod 8 of
  the primes of `β` (product `≡ 7`) and `θ` (product `≡ 1`), random symbols subject to reciprocity,
  (θ3) and (θ4), random sign. The slots are added symbolically. In 3,300 trials (300 with
  `ω(β), ω(θ) ≤ 6`, 1,000 with `≤ 12`, 2,000 with `≤ 3`) both systems had dimension 3 and contained
  the class `β`, with its sign.
- **Negative control.** With the wrong sign choice `x = s` instead of `x = s + 1`, the first curve is
  still certified and the second still has dimension 3, but `β` drops out of `π₁` in 183 of 300
  trials: exactly those where `θ` has a prime `≡ 3 (mod 4)`. So step 6 of the proof is sharp.
- **The gluing of `θ`** (`t1_transfer.py`): 200 random configurations of actual primes with a hub
  and partners; the two Selmer dimensions agreed in all 200.
- **Base configurations** (`t2_template.py`): exhaustive over classes and symbols; see §2.3.
- **Rational points** (`t4_ellrank.py`, PARI `ellrank`, effort 6). Ten small realizations of the
  construction (primes below 3000, with data satisfying (θ1)–(θ4), not coming from admissible `B`).
  `ellrank` gives the upper bound 1 for the rank of all 20 curves, consistent with `dim Sel₂ = 3`.
  It found explicit points on 6 curves (3 instances), and each has abscissa class `β` up to the
  torsion cosets. On the others `ellrank` found no point (its lower bound 1 is then not backed by a
  point); `ellheegner` was too slow at these conductors. This part tests the deep input on a few
  cases, not the descent.

### 3.4 What the computations do and do not show

They confirm the construction on every family requested, including all inputs on which earlier
methods failed (no certifying multiplier, isotropic cores, greedy stalls, smooth `θ`). They are not
the proof: §2 proves that the construction succeeds for every admissible `B`.

## 4. What the Lean proof would need

### 4.1 The narrowed hypothesis

Route K replaces `PoleCompleteness` by the version for `x + ℓ` (rv-route-k §2.2, §4.5). With DL proved,
the only input Lean cannot prove is the passage from a certificate of Selmer type to a rational point.
Mathlib has no Selmer groups. The hypothesis should therefore be stated with the explicit system of
§2.1, which only needs Legendre symbols of the primes of `d`. Write `𝒞_d` for the configuration of an
odd squarefree `d > 0`.

> **CR₃ (certified rank).** Let `d > 0` be odd and squarefree, and let `a` be a squarefree divisor of
> `±d`. Suppose the solution space of `Σ(𝒞_d)` has 8 elements (dimension 3) and contains a
> solution with first coordinate `a`. Then `C_d` has a rational point `(x, y)` with
> `x ∈ aℚ*²`.

Justification (not part of the Lean proof):

- Proposition 0 identifies `Σ(𝒞_d)` with `Sel₂(C_d)` (descent-alt §4.1; VERIFIED there, see §5
  for its status);
- Kriz, Theorems 10.13 and 10.17(2), with the corank lemma (manuscript line 1072; Poonen–Stoll,
  A019), gives `rank C_d(ℚ) = 1` and `Ш(C_d)[2] = 0` when `dim Sel₂ = 3`;
- pc-audit RK9: then `C_d(ℚ)/2C_d(ℚ) = Sel₂(C_d)`, so the class `a` comes from a point, which can be
  taken with `x ≠ 0`.

CR₃ can be narrowed further, at no cost to the proof:

- to `d ≡ 5 (mod 8)` and `|a| ≡ 7 (mod 8)`, since the construction only produces such pairs
  (`|n| ≡ 7·3`, `|β| ≡ 7`);
- to the `d` whose configuration has the shape of §2.4 (a glued base `{p*, q₀}`). This restriction
  does not make the deep input weaker in any useful sense, so it is not recommended.

The first restriction is exactly the K-TYZ-β rule of pc-audit §4.2. If pc-audit's RK6 analysis of
TYZ row 5b is confirmed, CR₃ in this restricted form follows from Tian–Yuan–Zhang Theorem 1.2 plus
Gross–Zagier–Kolyvagin (A020), both published, without Kriz (SPECULATIVE until RK6 is checked).

### 4.2 The lemmas Lean would prove

| Lemma | Content | Main Mathlib inputs |
| --- | --- | --- |
| L1 (multiplier) | for admissible `B` some signed divisor `m` of 2730 gives `β` odd with `|β| ≡ 7 (mod 8)` | finite case analysis on `v₂` and residues mod 8; `decide` over the 64 divisors |
| L2 (θ1)–(θ4) | properties of `θ` from `θc² = 1 − βt²` | valuations (`padicValRat`), `ZMod` squares; parts are already in the valuation lemmas of `PoleObstruction.lean` |
| L3 (slots) | existence of `q₀`, `r_p`, `r_ℓ` with prescribed residue conditions, distinct and outside `2βθ` | Dirichlet: `Nat.forall_exists_prime_gt_and_zmodEq` (`NumberTheory/LSeries/PrimesInAP.lean`); CRT: `Nat.chineseRemainderOfList`; non-residues: `FiniteField.exists_nonsquare`, `legendreSym.eq_neg_one_iff` |
| L4 (system) | definition of `Σ(𝒞)` for a finite configuration; Lemmas 1 and 2 as bijections of solution sets; Lemma 3 by `decide` | `Finset` sums in `ZMod 2`, `Fintype.card` of solution sets under bijections |
| L5 (realization) | the configuration of `d₁`, `d₂` is the abstract one: symbols of products, the reverse symbols, the Jacobi step `(p/θ) = (θ/p)` | `legendreSym.mul`, `jacobiSym.quadratic_reciprocity_one_mod_four`, `jacobiSym.at_neg_one`, `jacobiSym.at_two` |
| L6 (points to `PoleSoluble`) | two points with abscissa in `βℚ*²` on `C_n`, `C_{nθ}` give a zero of the `x + ℓ` pole polynomial | the algebra of rv-route-k §4.2 (`reform_check.py`), done once by `ring`/`field_simp` |

The chain is `L1, L2, L3 ⇒ (configurations); L4, L5 ⇒ the systems have dimension 3 and contain the
class β; CR₃ ⇒ points; L6 ⇒ PoleSoluble`.

### 4.3 The hardest steps to formalize

- **L4, the gluing bijection.** The proof of Lemma 2 is short on paper but manipulates sums over a
  configuration whose index set changes (`S` versus `S' ⊔ {g*}`), with the diagonal of `K` built from
  row sums. In Lean the clean route is to index configurations by a `Fintype`, prove Lemma 2 for an
  abstract index type `S' ⊕ Unit ⊕ G ⊕ G` (glue primes indexed by `G`), and transport along
  equivalences. This is the largest piece; it is elementary but bookkeeping-heavy.
- **L5, from actual primes to the abstract configuration.** Every symbol of the configuration of
  `d₁` and `d₂` has to be computed from the residue conditions of L3: the reverse symbols by
  reciprocity, the symbols of `θ` and `|β|` by multiplicativity of the Jacobi symbol, and the classes
  mod 8 by `χ₄`, `χ₈`. Mathlib has every ingredient; the cost is the number of cases.
- **L3, choosing the slots.** Dirichlet and CRT are available. The Lean statement must produce a
  `List` of primes with a pairwise condition, by recursion on the primes of `β` and `θ`, and prove
  distinctness and squarefreeness of the product.
- **CR₃ itself** is a hypothesis, so no Selmer theory enters Lean. Its proof from Kriz requires
  Proposition 0, which identifies the explicit system with `Sel₂(C_d)`. That identification is the
  natural next target if one later wants a Lean statement in terms of genuine Selmer groups; Mathlib
  currently has neither Galois cohomology of elliptic curves nor local images, so it is out of reach
  for now (SPECULATIVE effort estimate: months).

The elementary part (L1–L6) has no analytic or cohomological content. Following pc-audit §4.4, a
SPECULATIVE estimate is a few weeks of formalization.

## 5. Assessment

### 5.1 Is the proof complete?

**DL is true, and §2 proves it** (VERIFIED). The proof uses:

- the explicit 2-descent of Proposition 0. The rows actually used are the odd places and the real
  place (proved by hand in descent-alt §4.1), the structure of the place-2 rows, and the explicit
  rows for `c = 5`. The last two are rechecked by hand in §2.1;
- quadratic reciprocity and its supplements, for Legendre and Jacobi symbols (STANDARD);
- the Chinese remainder theorem and Dirichlet's theorem (STANDARD; A057);
- the properties (θ1)–(θ4) of the input pairs (descent-alt §3.1; manuscript lines 1027–1033).

No step uses the witness `q`, and no step depends on the size of `θ` or on its symbols beyond
(θ1)–(θ4). The construction is uniform: it treats both call sites at once, for every admissible `B`.

Computations (§3) confirm the construction on every requested family with the exact descent, and
confirm the theorem itself on 3,300 random abstract configurations, including up to 12 primes in each
of `β` and `θ`.

**Where a reviewer should look hardest.**

1. *Lemma 2, step 3.* It sums the rows over the glued set `X`, so that the glue unknowns `u_{r_ℓ}`
   cancel. The cancellation needs `u_ℓ = u_g` for all `ℓ ∈ G`, which comes from step 1. The terms
   inside `X` vanish because they come in the form `[x'/x](u_{x'} + u_x)` with equal values; no
   symmetry of the symbols among `X` is needed.
2. *Step 5 of the theorem.* The identification of the glued `θ`-configuration with `𝒞_Σ` uses
   (θ4) twice: once directly for `[θ/p]`, once through Jacobi reciprocity for `[p/θ]`. It uses that
   the `r_p` have trivial symbols at `T`, and that `θ ≡ 1 (mod 8)` keeps the class of `q₀`.
3. *The sign bookkeeping in step 6.* `u_{r_ℓ} = λ_ℓ(s + x + 1)` vanishes only because `x = s + 1`.
   The negative control of §3.3 shows that the opposite choice fails exactly when `θ` has a prime
   `≡ 3 (mod 4)`.
4. *Proposition 0 itself.* descent-alt determined the place-2 table by computing images from sampled
   2-adic points until dimension 3 was reached. §2.1 replaces this, for what the proof needs, by a
   direct argument. The rows for `c = 1, 3, 7` are never used: Lemmas 1–2 use only the structure of
   the rows, and every curve the construction produces has `c = 5`. Those rows rest only on
   descent-alt's 600-curve check.

**A first independent check.** A separate reviewer, given only §§1–2 and the code, redid
Lemmas 1–3, the place-2 rows for `c = 5`, (θ1)–(θ4) and steps 0–6 by hand. It found no error. Its
only remark was that the `v`-analogue (2.2) of (2.1) should be written out, which is now done. It
also tested Lemma 2 on 3,000 random virtual configurations, comparing dimensions and checking (2.1)
on every kernel vector, and ran the end-to-end construction with real primes below 300,000 on 558
curves (`symsel.py`). There were no failures. This was an automated review, not the human review
Jack requires.

Per Jack's decision, the Lean construction switches to `x + ℓ` only once this proof survives an
independent review. The review is the remaining step.

### 5.2 What DL does not settle

- **The deep input.** The certificates give points only through Kriz's 2-converse (an unrefereed
  preprint; pc-audit RK1), with Poonen–Stoll (A019). Alternatively, through TYZ and Gross–Zagier, if
  the row-5b rule of pc-audit RK6 holds. The construction automatically lands in that rule
  (`|n| ≡ 5 (mod 8)`, `|β| ≡ 7`), so it needs no change for the TYZ variant (§2.6).
- **The written manuscript.** Section 5's descent (lines 1019–1121) would be rewritten for `C_ℓ`
  along §2. The manuscript's slot count (`d − 1` slots plus `q₀`) and the role of `q₀` carry over;
  the `θ`-slots are new.

### 5.3 Open questions

- **The minimal number of slots.** The construction uses `ω(β) + ω(θ)`. Proposition B forces at
  least `k(β)`, the size of an isotropic core, and random searches typically find 2–4. Does
  `ω(β) + O(1)` always suffice, i.e. can the `θ`-slots be avoided? Since the witness `q` cannot
  control `θ`, a bound independent of `θ` would need a different way to make the second curve
  inherit the Selmer group of the first.
- **Other base configurations.** Lemma 3 is the only base with one auxiliary prime, and it forces
  `|β| ≡ 3, 7 (mod 8)`. Bases with two auxiliary primes exist for `|β| ≡ 1, 5` (`t2_template.py`).
  They would allow the other multipliers, which matters only if a later variant restricts `m`.
- **A Selmer-free deep input.** CR₃ (§4.1) is stated through the explicit system. If one wants the
  Lean hypothesis to mention genuine Selmer groups, Proposition 0 must be formalized first.

## Scripts (in `scratch/slot-k/`)

| Script | Purpose | Output |
| --- | --- | --- |
| `slotk.py` | the construction of §2.4 with actual primes; certification by `sel2cong.py` | |
| `run_dl.py` | driver, random admissible inputs | `out_random30.txt` |
| `run_families.py` | drivers for `B123`, `e11`, `core3`, `core6`, `stall`, `smooth`, `allm` | `out_<family>.txt` |
| `summarize.py` | the table of §3.2 | |
| `find_seed_e8.py`, `e8_replay.py` | recover and replay descent-alt's greedy descent, printing the inputs | `out_e8_replay.txt` |
| `t1_transfer.py` | the gluing of `θ` onto an auxiliary prime, on actual primes | |
| `t2_template.py` | exhaustive search of base configurations (§2.3) | |
| `t3_symbolic.py` | the theorem on random abstract data; `WRONGX=1` gives the negative control | |
| `t4_ellrank.py` | PARI `ellrank` on small realizations | `out_t4_ellrank.txt` |
| `t_one.py` | timing of one instance | |

PARI is used through `cypari2` (for factoring `θ`, Jacobi symbols in the prime search, and `ellrank`).
