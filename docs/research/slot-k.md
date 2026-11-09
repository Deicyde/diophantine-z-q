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

### 1.2 Certificates (VERIFIED, descent-alt Notation and §2(c); rv-route-k §4.3)

For squarefree `d` and the class `β`, a **certificate** for `C_d` is one of:

- (torsion) `d ≡ ±β` modulo squares; then `(β, 0)` or `(−β, 0)` lies on `C_d` up to the
  identification `C_d ≅ C_{−d}`; or
- (Selmer) `dim_{𝔽₂} Sel₂(C_d) = 3` and `β ∈ π₁(Sel₂(C_d))`.

In the Selmer case, Kriz's 2-converse (arXiv:2002.04767v5, Theorems 10.13 and 10.17(2)) together
with the corank lemma (manuscript Lemma 5.3 at line 1072; Poonen–Stoll, audit record A019) gives
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

- The rows at odd `p | d` are the local conditions at `p`: the local image is spanned by the
  torsion images, and `E1_p`, `E2_p` say that the unit parts of `a`, `b` at `p` have the residue
  symbols `u_p[d/p · p⁻¹ … ]` prescribed by the four valuation patterns.
- `(R)` is the real place for `d > 0`; `(D)` is the place 2, read off from the 2-adic image.
- descent-alt checked the system against an independent exact descent (`sel2cong.py`, itself
  checked against PARI in rv-route-k) on 600 curves with 0 mismatches.

Only two structural features of `(D)` are used below: it depends on `𝒞` only through `c(𝒞)`, and on
`u, v` only through the sums `λ·u`, `μ·u`, `λ·v`.

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
nothing to `λ·u`, `μ·u`, `λ·v`. ∎

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

with `a₁ = 0`, which `(D)` forces.

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
   `λ·u = λ|_{S'}·u|_{S'} + λ_{g*}u_g`, and likewise for `μ·u` and `λ·v`. So `(D)` and `(R)` are the
   same on both sides.

So `Φ` maps solutions to solutions. It is injective: if the image is 0, then `u_X = v_X = 0` by step 1,
and (2.1) and its `v`-analogue give `u_R = v_R = 0`. It is surjective: given a solution of `Σ(𝒞*)`, set
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

The pair `(7, 3)` is the classical one: for primes `p ≡ 7`, `q ≡ 3 (mod 8)`, `pq ≡ 5 (mod 8)` and
`Sel₂(C_{pq})` has dimension 3 (Monsky, appendix to Heath-Brown, Invent. Math. 118 (1994); STANDARD).
