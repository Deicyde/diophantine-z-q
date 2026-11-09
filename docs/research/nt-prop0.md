# Proposition 0 in Lean: the 2-Selmer group of `C_d` through 2-coverings

Hypothesis CR₃ (`ZInQ.CertifiedRank`, `ZInQKernel/Hypotheses/CertifiedRank.lean`) is stated through
the explicit system `Σ(𝒞_d)` of `ZInQKernel/RouteK/System/Selmer.lean` (`Config.IsSol`, rows `E1`,
`E2`, `(R)` and `twoAdicRows`). Its justification passes through Proposition 0 (descent-alt §4.1,
refereed in rv-slot-k-descent §1.1–1.5, checked in slot-k §2.1): the solutions of `Σ(𝒞_d)` are the
elements of `Sel₂(C_d)` for `C_d : y² = x³ − d²x`. This note works out what a Lean proof of
Proposition 0 needs and how the hypothesis would then read.

## Summary

- **Definition** (§1). `Sel₂(C_d)` is defined as the set of pairs `(a, b)` of squarefree integers whose
  2-covering `D_{a,b} : a z₁² − b z₂² = d w², a z₁² − ab z₃² = −d w²` has a point over `ℝ` and over every
  `ℚ_p`. An elementary lemma valid over any field of characteristic `≠ 2` (Lemma 1.2) shows that
  `D_{a,b}(K) ≠ ∅` exactly when `(a, b)` lies in the image of the explicit Kummer map
  `δ_K : C_d(K) → (K*/K*²)²`. Combined with Silverman X.1.4 (the formula for `δ` is the connecting
  map), this is the textbook Selmer group. Lean can state it with `ℚ_[p]`, `ℝ` and `IsSquare` only.
- **Literature form of the hypothesis** (§1.4). With Proposition 0 proved, CR₃ follows in Lean from
  `CR₃^Sel`: *if `d ≡ 5 (mod 8)` is squarefree, `#Sel₂(C_d) = 8` and `Sel₂(C_d)` contains a pair
  `(a, b)` with `|a| ≡ 7 (mod 8)`, then every element of `Sel₂(C_d)` has a rational point on its
  covering.* Given Silverman X.1.4, `CR₃^Sel` is equivalent to `rank C_d(ℚ) ≥ 1` for these `d`, which is
  what Tian–Yuan–Zhang with Gross–Zagier–Kolyvagin, or Kriz's 2-converse, provide.
- **Local computations** (§2). All four kinds of places reduce to elementary arguments in the
  "x-form" of the covering (`x/a`, `(x − d)/b`, `(x + d)/(ab)` all squares). At an odd `p | d` and at
  the real place, the local image is spanned by the torsion images, and a case analysis on the
  valuation of `x` proves it. At `2`, for `d ≡ 5 (mod 8)`, there are eight classes: four torsion
  classes and the four classes of the points with `x = 1/4`, `−4d²`, `d(1 + 4d)/(1 − 4d)` and
  `−d(1 − 4d)/(1 + 4d)`. The necessity half is a case analysis on `v₂(x)` and `x mod 8`.
- **The good primes need neither the group law nor the Hasse bound** (§2.4, new). Here sufficiency
  means that every unit pair is locally soluble at `p ∤ 2d`. It follows from a character-sum count
  over `𝔽_p`, Jacobsthal's identity `Σ_n S(n)² = p(p − 1)(1 + χ(−1))` for
  `S(n) = Σ_x χ(x³ − nx)` (an elementary orthogonality computation, which gives `|S(d²)| ≤ 2√p`), a
  finite check for `p < 29`, and Hensel's lemma for units. Necessity at these primes (no class is
  ramified at `p ∤ 2d`) uses valuations only.
- **Mathlib** (§3) has `ℚ_[p]`, `ℤ_[p]`, Hensel's lemma for polynomials over `ℤ_[p]`, Legendre and
  Jacobi symbols, quadratic characters and Weierstrass curves with their group law. It has no
  Hilbert symbol, no square-class criterion for `ℚ_p`, no 2-descent and no Selmer group. The main
  missing pieces are short: the unit-square criteria for `ℚ_p` and `ℚ₂`, and the sum of `χ` over a
  quadratic polynomial.
- **Plan** (§4). About 2,500–4,000 lines in eight files, in three tiers. The first step, the
  square-class criterion for `ℚ_p` and the real and `p | d` places, would show that the case
  analyses over `ℚ_p` are manageable in Lean.

Status labels: VERIFIED (checked against the text or by a computation), STANDARD (a published
theorem whose statement was checked to apply, with its reference), SPECULATIVE (unproved),
UNCHECKED (the source could not be read). Scripts are in `scratch/nt-prop0/`.

## 0. Notation

- `d > 0` is odd and squarefree, with prime set `S`, and `C_d : y² = x(x − d)(x + d)`, so
  `e₁ = 0`, `e₂ = d`, `e₃ = −d`. The 2-torsion points are `T₁ = (0, 0)`, `T₂ = (d, 0)`, `T₃ = (−d, 0)`.
- For a field `K`, `□_K` is the set of squares of `K`, **including 0**. `a ≡ a'` in `K*` means
  `a/a' ∈ K*²`.
- A solution `σ = (a₀, a₁, b₀, b₁, u, v)` of `Σ(𝒞_d)` stands for the integers
  `a(σ) = (−1)^{a₀} 2^{a₁} Π_{p∈S} p^{u_p}` and `b(σ) = (−1)^{b₀} 2^{b₁} Π_{p∈S} p^{v_p}`, as in the
  docstring of `Selmer.lean` and in rv-slot-k-descent §1.1. `λ_p = [−1/p]`, `μ_p = [2/p]`,
  `[y/x] = legBit x y` (`RouteK/Slots/Symbols.lean`, line 17).
- For an odd prime `p` and `r ∈ ℚ_p*`, the *class* of `r` is `(v_p(r) mod 2, [r'/p])`, where `r'` is the
  unit part. For `p = 2` it is `(v₂(r) mod 2, r' mod 8)`. The Kummer classes at `2` are written by
  their integer representatives in `{1, 3, 5, 7, 2, 6, 10, 14}`.

## 1. The definition of `Sel₂(C_d)`

### 1.1 The coverings (VERIFIED)

For a field `K` of characteristic `≠ 2` and `a, b ∈ K*`, let `D_{a,b} ⊂ ℙ³` be the curve

```
a z₁² − b z₂² = d w²,        a z₁² − ab z₃² = −d w².
```

These are Silverman's equations `b₁z₁² − b₂z₂² = e₂ − e₁`, `b₁z₁² − b₁b₂z₃² = e₃ − e₁` (*The Arithmetic of
Elliptic Curves*, X.1.4, as cited and checked in rv-slot-k-descent §1.1), with `w` added to make the
curve projective. Rescaling `z₁, z₂, z₃` by `s`, `t`, `st` shows that `D_{a,b} ≅ D_{as², bt²}` over `K`.
So the solubility of `D_{a,b}` depends only on the classes of `a` and `b` in `K*/K*²` (VERIFIED).

Two reformulations are used throughout.

- **x-form.** `D_{a,b}(K) ≠ ∅` if and only if `a, b ∈ K*²`, or there is `x ∈ K` with
  `x/a ∈ □_K`, `(x − d)/b ∈ □_K` and `(x + d)/(ab) ∈ □_K`.
- **Points at infinity.** A point with `w = 0` exists if and only if `a, b ∈ K*²`.

*Proof.* Let `(z₁ : z₂ : z₃ : w)` be a point. If `w = 0`, then `a z₁² = b z₂²` and `z₁² = b z₃²`. Here
`z₁ ≠ 0`, since otherwise all coordinates vanish. So `b = (z₁/z₃)²` and `a = b(z₂/z₁)²` are nonzero
squares. Conversely, if `a = s²` and `b = t²`, then `(1/s : 1/t : 1/(st) : 0)` is a point. If `w ≠ 0`,
put `x = a(z₁/w)²`. Then `(x − d)/b = (z₂/w)²` and `(x + d)/(ab) = (z₃/w)²`. Conversely, if
`x/a = r₁²`, `(x − d)/b = r₂²` and `(x + d)/(ab) = r₃²`, then `(r₁ : r₂ : r₃ : 1)` is a point, because
`a r₁² − b r₂² = x − (x − d)` and `a r₁² − ab r₃² = x − (x + d)`. ∎

### 1.2 Coverings and the Kummer map (VERIFIED)

Define `δ_K : C_d(K) → (K*/K*²)²` by the usual formula:

- `δ(O) = (1, 1)`;
- `δ(T₁) = (−1, −d)`, from `((e₁ − e₂)(e₁ − e₃), e₁ − e₂) = (−d², −d)`;
- `δ(T₂) = (d, 2)`, from `(e₂ − e₁, (e₂ − e₁)(e₂ − e₃)) = (d, 2d²)`;
- `δ(T₃) = (−d, −2d)`;
- `δ(x, y) = (x, x − d)` otherwise.

These are the values listed in rv-slot-k-descent §1.1.

**Lemma 1.2.** For every field `K` of characteristic `≠ 2` and all `a, b ∈ K*`:
`(a, b) ≡ δ_K(P)` for some `P ∈ C_d(K)` if and only if `D_{a,b}(K) ≠ ∅`.

*Proof.* Use the x-form of §1.1.

- (⇐) If `a, b ∈ K*²`, take `P = O`. Otherwise take `x` as in the x-form, and put
  `y = ab r₁r₂r₃`. Then `y² = (a r₁²)(b r₂²)(ab r₃²) = x(x − d)(x + d)`, so `P = (x, y) ∈ C_d(K)`.
  - If `x ∉ {0, ±d}`, then `r₁, r₂ ≠ 0` and `δ(P) = (a r₁², b r₂²) ≡ (a, b)`.
  - If `x = 0`, then `−d/b = r₂²` and `d/(ab) = r₃²` with `r₂, r₃ ≠ 0`. So `b ≡ −d`, `ab ≡ d`, hence
    `a ≡ −1` and `(a, b) ≡ δ(T₁)`.
  - If `x = d`, then `a ≡ d` and `ab ≡ 2d`, so `b ≡ 2`, which is `δ(T₂)`.
  - If `x = −d`, then `a ≡ −d` and `b ≡ −2d`, which is `δ(T₃)`.
- (⇒) By the rescaling invariance it suffices to treat `(a, b) = δ(P)` itself.
  - For `P = O`, use the point at infinity.
  - For `T₁ = (0,0)`, `(a, b) = (−1, −d)`: take `x = 0`, with `0/a = 0`, `−d/b = 1` and
    `d/(ab) = 1`. On the covering this is the point `(0 : 1 : 1 : 1)`.
  - For `T₂`, `(a, b) = (d, 2)`: take `x = d`, which gives the point `(1 : 0 : 1 : 1)`.
  - For `T₃`, `(a, b) = (−d, −2d)`: take `x = −d`, which gives the point `(1 : 1 : 0 : 1)`.
  - For `P = (x, y)` with `x ∉ {0, ±d}`, `(a, b) = (x, x − d)`: then `x/a = 1`, `(x − d)/b = 1` and
    `(x + d)/(ab) = y²/(x(x − d))²`. ∎

The lemma holds over every field of characteristic `≠ 2` and uses no group law. In Lean it is a
`field_simp`/`ring` exercise, generic in `K` (VERIFIED by hand; the explicit points are also checked
in `scratch/nt-prop0/t_two_adic.py` for `K = ℚ₂`).

### 1.3 The definition, and why it is the standard one

**Definition.** For odd squarefree `d > 0`, `Sel₂(d)` is the set of pairs `(a, b) ∈ ℤ²` with `a` and `b`
squarefree (signs allowed, so `a, b ≠ 0`) such that `D_{a,b}(ℝ) ≠ ∅` and `D_{a,b}(ℚ_p) ≠ ∅` for every
prime `p`.

The textbook definition (Silverman X.4) is `Sel₂(E/ℚ) = {ξ ∈ H¹(ℚ, E[2]) : res_v ξ ∈ δ_v(E(ℚ_v)) for
all v}`. The definition above agrees with it for three reasons.

1. Full 2-torsion and Kummer theory identify `H¹(ℚ, E[2])` with `(ℚ*/ℚ*²)²`. Under this identification
   the connecting map is the formula for `δ` of §1.2, by Silverman X.1.4 (STANDARD; the statement as
   used in rv-slot-k-descent §1.1). The same holds over every `ℚ_v`, compatibly with restriction.
2. Every class in `ℚ*/ℚ*²` has exactly one squarefree integer representative (elementary).
3. Lemma 1.2 over `K = ℚ_v` turns the condition `res_v ξ ∈ δ_v(E(ℚ_v))` into `D_{a,b}(ℚ_v) ≠ ∅`.

So the only non-Lean input in "this set is `Sel₂(C_d/ℚ)`" is the first point: the identification of
`H¹` with pairs of square classes and of the connecting map with the explicit formula. This is the
first page of every treatment of complete 2-descent. A referee would accept it, as rv-slot-k-descent
§1.1 did. Mathlib has no Galois cohomology of elliptic curves, so this point cannot be formalized
now, and it need not be.

A second, equivalent wording avoids `H¹` altogether. `Sel₂` is then the set of everywhere locally
soluble 2-coverings of `C_d` of the shape `D_{a,b}` (Cassels' formulation). The two wordings agree by
Lemma 1.2 and the fact that every 2-covering of a curve with full 2-torsion is isomorphic to one
`D_{a,b}` (STANDARD; Silverman X.1.4, X.3). The Lean definition is the same in both cases.
