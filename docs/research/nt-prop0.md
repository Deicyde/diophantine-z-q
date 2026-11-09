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
`D_{a,b}` (STANDARD in substance, Silverman X.3; the exact statement there is UNCHECKED here). The Lean definition is the same in both cases.

### 1.4 The hypothesis in the literature's form

With `Sel₂(d)` as in §1.3 and `Loc_K(a, b)` the x-form condition of §1.1, the narrowed hypothesis reads:

> **CR₃^Sel.** Let `d > 0` be squarefree with `d ≡ 5 (mod 8)`. If `Sel₂(d)` has exactly 8 elements
> and contains a pair `(a, b)` with `|a| ≡ 7 (mod 8)`, then `D_{a',b'}(ℚ) ≠ ∅` for every
> `(a', b') ∈ Sel₂(d)`.

In Lean (SPECULATIVE wording, to be fixed in the first file of §4):

```lean
def Sel2 (d : ℕ) : Set (ℤ × ℤ) :=
  {ab | Squarefree ab.1 ∧ Squarefree ab.2 ∧ Loc ℝ d ab.1 ab.2 ∧
        ∀ p : ℕ, (hp : p.Prime) → haveI := Fact.mk hp; Loc ℚ_[p] d ab.1 ab.2}

def CertifiedRankSel : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → (Sel2 d).ncard = 8 →
    (∃ ab ∈ Sel2 d, ab.1.natAbs % 8 = 7) → ∀ ab ∈ Sel2 d, Loc ℚ d ab.1 ab.2
```

where `Loc K d a b := (IsSquare (a : K) ∧ IsSquare (b : K)) ∨ ∃ x : K, IsSquare (x / a) ∧
IsSquare ((x - d) / b) ∧ IsSquare ((x + d) / (a * b))`.

**What `CR₃^Sel` says in the literature's terms** (given Silverman X.1.4, STANDARD). By Lemma 1.2 over
`ℚ`, the conclusion says `δ(C_d(ℚ)) = Sel₂(C_d)`, that is `Ш(C_d)[2] = 0`. Since `δ` induces an injection
`C_d(ℚ)/2C_d(ℚ) → Sel₂` and `C_d(ℚ)[2] = C_d[2]` has order 4, `dim δ(C_d(ℚ)) = 2 + rank C_d(ℚ)`. So
under `dim Sel₂ = 3` the conclusion is equivalent to `rank C_d(ℚ) ≥ 1`, i.e. to `d` being a congruent
number. The sources named in the docstring of `ZInQ.CertifiedRank` give this:

- Kriz's 2-converse (arXiv:2002.04767, Theorem 10.13) with the corank lemma;
- or, under exactly the hypothesis `|a| ≡ 7 (mod 8)`, Tian–Yuan–Zhang (Theorem 3.5(2)) with
  Gross–Zagier–Kolyvagin (docs/research/tyz-5b.md).

Both routes are STANDARD as recorded there; this note does not recheck them. Compared with CR₃ the
gain is that the explicit system, Legendre symbols and Monsky matrices disappear from the trust
boundary. What remains is the textbook definition of `Sel₂` and the statement "Selmer rank 3 implies
rank 1" for these curves.

**CR₃ from `CR₃^Sel` and Proposition 0 (VERIFIED on paper, all steps elementary).** Assume the
hypotheses of `ZInQ.CertifiedRank`: `d ≡ 5 (mod 8)` squarefree, `a` a squarefree divisor of `d` with
`|a| ≡ 7 (mod 8)`, `(natConfig d _).sols.card = 8`, and `σ ∈ sols` with `σ.first = natClass d a`.

1. Proposition 0 (§2.8) gives a bijection `sols ≃ Sel₂(d)`, `σ ↦ (a(σ), b(σ))`. So
   `(Sel2 d).ncard = 8`.
2. `σ.first = natClass d a` means `a₀ = [a < 0]`, `a₁ = 0` and `u_p = [p | a]`. Because `a` is a
   squarefree divisor of `d`, this gives `a(σ) = a`. So `(a, b(σ)) ∈ Sel₂(d)` with `|a| ≡ 7`.
3. `CR₃^Sel` gives `Loc_ℚ(a, b(σ))`. The first alternative is impossible: `a ∈ ℚ*²` with `a`
   squarefree forces `a = 1`. So there is `x ∈ ℚ` with `x/a = r₁²`, `(x − d)/b = r₂²` and
   `(x + d)/(ab) = r₃²`.
4. `x ≠ 0`. Otherwise `−d/b` and `d/(ab)` are nonzero squares, so `a ≡ −1`, which forces `a = −1`,
   against `|a| ≡ 7`.
5. `y = a b r₁ r₂ r₃` satisfies `y² = x³ − d²x` (by `ring`), and `x/a = r₁²` is a square.

This is the conclusion of `CertifiedRank`. In Lean, steps 3–5 take a few dozen lines; step 2 is a
factorization argument on squarefree integers (`Int.squarefree`, `Nat.prod_primeFactors_of_squarefree`).

## 2. The local computations, in the order Lean needs them

Throughout, `Loc_K(a, b)` is the x-form condition of §1.1. Two remarks are used everywhere.

- **(Inv)** If `a = a's²` and `b = b't²` with `s, t ∈ K*`, then `Loc_K(a, b) ⟺ Loc_K(a', b')`, with the same
  `x`: divide the three squares by `s²`, `t²` and `(st)²` (VERIFIED). So `Loc` depends only on the classes.
- **(Tor)** If the first alternative fails and the witness is `x ∈ {0, d, −d}`, then `(a, b)` is
  respectively `(−1, −d)`, `(d, 2)` or `(−d, −2d)` up to squares (proof of Lemma 1.2). Otherwise `x`,
  `x − d`, `x + d` are nonzero, `x ≡ a`, `x − d ≡ b`, `x + d ≡ ab`, and `x(x − d)(x + d) ∈ K*²`.

### 2.1 Square classes of `ℚ_p` (VERIFIED on paper; Mathlib inputs in §3)

**Lemma SQ.**

- (a) Let `p` be odd and `u ∈ ℤ_p*`. Then `u ∈ ℚ_p*²` if and only if its residue `ū ∈ 𝔽_p` is a square.
- (b) Let `u ∈ ℤ₂*`. Then `u ∈ ℚ₂*²` if and only if `u ≡ 1 (mod 8)`.
- (c) A nonzero `r = p^k u` (with `u` a unit) is a square if and only if `k` is even and `u` is a square.

*Proof.*

- (a) (⇒) If `u = r²`, then `|r| = 1`, so `r ∈ ℤ_p`, and we reduce mod `p`. (⇐) Pick `a ∈ ℤ_p` with
  `ā² = ū`. Then `F = X² − u` has `|F(a)| < 1 = |F′(a)|²`, since `F′(a) = 2a` is a unit. Hensel's lemma
  gives a root.
- (b) (⇐) Take `a = 1`: `|F(1)| = |1 − u| ≤ 2⁻³ < 2⁻² = |F′(1)|²`. (⇒) An odd `r` has `r² ≡ 1 (mod 8)`.
- (c) Valuations.

Two consequences are used in the case analyses.

- **Perturbation (P).** If `p` is odd and `|y| < |x|`, then `(x + y)/x ∈ ℚ_p*²`, since `1 + y/x ≡ 1` mod
  `p`. If `p = 2` and `|y| ≤ 2⁻³|x|`, the same holds, since `1 + y/x ≡ 1 (mod 8)`.
- **Rational test (RT).** A rational number whose numerator and denominator are prime to `p`, and
  whose residue is a square mod `p` (respectively `≡ 1 (mod 8)` when `p = 2`), is a square in `ℚ_p`.

### 2.2 The real place (VERIFIED)

**Lemma ∞.** `Loc_ℝ(a, b)` holds if and only if `a` and `b` have the same sign. This is row `(R)`,
`a₀ = b₀`.

*Proof.*

- If `a, b > 0`, take `x = d`: `x/a ≥ 0`, `x − d = 0`, `x + d > 0`. If `a, b < 0`, take `x = 0`.
- Conversely, suppose `a > 0 > b`. Then `x ≥ 0`, `x − d ≤ 0` and `(x + d)/(ab) ≥ 0`, so `x + d ≤ 0`, which
  contradicts `x ≥ 0`. Suppose `a < 0 < b`. Then `x ≤ 0` and `x − d ≥ 0`, which contradicts `d > 0`.
  The first alternative of `Loc` forces `a, b > 0`. ∎

In Lean this is `Real.isSquare_iff` (nonnegativity) followed by `nlinarith`-sized arguments.

### 2.3 Odd primes not dividing `d` (VERIFIED on paper; computations below)

**Lemma G1 (no ramification).** Let `p ∤ 2d`. If `Loc_{ℚ_p}(a, b)`, then `v_p(a)` and `v_p(b)` are even.

*Proof.*

- First alternative: clear.
- Witness `x ∈ {0, ±d}`: the classes `(−1, −d)`, `(d, 2)`, `(−d, −2d)` are units at `p`.
- Otherwise `v(x) ≡ v(a)`, `v(x − d) ≡ v(b)` and `v(x + d) ≡ v(a) + v(b)` (mod 2). Three cases:
  - If `v(x) < 0`, all three valuations equal `v(x)`, so `v(a) ≡ v(b) ≡ v(x) ≡ 2v(x) ≡ 0`.
  - If `v(x) > 0`, then `v(x ∓ d) = 0`, so `v(b) ≡ 0` and `v(a) ≡ 0`.
  - If `v(x) = 0`, then `v(a)` is even. At most one of `x − d`, `x + d` is divisible by `p`, because
    their difference `2d` is a unit. Whichever is a unit forces `v(b)` or `v(a) + v(b)` to be even. ∎

**Lemma G2 (unit pairs are soluble).** Let `p ∤ 2d` and let `a, b` be prime to `p`. Then `Loc_{ℚ_p}(a, b)`.

The proof has three steps: a statement over `𝔽_p`, a count, and a lift.

*Step 1 (the statement over `𝔽_p`).* It suffices to find `ξ ∈ 𝔽_p` such that `ξ/ā`, `(ξ − d̄)/b̄` and
`(ξ + d̄)/(āb̄)` are squares in `𝔽_p` (zero allowed), or else that `ā, b̄` are squares. Given such a `ξ`,
the lift is as follows.

- If `ξ ∉ {0, ±d̄}`, take any `x ∈ ℤ` with `x̄ = ξ`. Then `x/a`, `(x − d)/b` and `(x + d)/(ab)` are
  `p`-adic units with square residues, hence squares by SQ(a).
- If `ξ = 0`, `d̄` or `−d̄`, take `x = 0`, `d` or `−d` exactly. The two nonzero quantities are units with
  square residues.
- If `ā, b̄` are squares, then `a, b ∈ ℚ_p*²` by SQ(a).

*Step 2 (counting, for `p ≥ 29`).* Let `χ` be the quadratic character of `𝔽_p`, `α = χ(ā)`, `β = χ(b̄)`,
and `N` the number of `ξ ∉ {0, ±d̄}` with `χ(ξ) = α`, `χ(ξ − d̄) = β` and `χ(ξ + d̄) = αβ`. Then

```
8N = Σ_{ξ ∉ {0,±d̄}} (1 + αχ(ξ)) (1 + βχ(ξ − d̄)) (1 + αβχ(ξ + d̄)).
```

Expanding:

- the constant term is `p − 3`;
- each of the three linear sums `Σ′ χ(ξ − e)` equals `0` minus two excluded terms of absolute value 1;
- each of the three quadratic sums `Σ′ χ((ξ − e)(ξ − e′))` equals `−1` minus one excluded term;
- the cubic term has coefficient `α²β² = 1` and equals `S(d̄²)`, where `S(n) = Σ_{ξ∈𝔽_p} χ(ξ³ − nξ)`
  (its excluded terms vanish).

Hence `8N ≥ p − 15 − |S(d̄²)|`.

The quadratic sums use **Lemma Q**: `Σ_ξ χ((ξ − e)(ξ − e′)) = −1` for `e ≠ e′`. Substituting
`ξ = e + (e′ − e)t` turns it into `Σ_t χ(t(t − 1)) = χ(−1) J(χ, χ)`, and Mathlib's
`jacobiSum_nontrivial_inv` gives `J(χ, χ⁻¹) = −χ(−1)`, with `χ⁻¹ = χ`.

**Lemma J (Jacobsthal).** `S(d̄²)² ≤ 4p`.

*Proof.*

- (1) `S(nt²) = χ(t)S(n)` for `t ≠ 0`. Substitute `ξ = tη`, so that `ξ³ − nt²ξ = t³(η³ − nη)`. Hence
  `S(n)²` depends only on the square class of `n`, and `S(d̄²)² = S(1)²`.
- (2) `S(0) = Σ χ(ξ)³ = 0`.
- (3) `Σ_{n∈𝔽_p} S(n)² = p(p − 1)(1 + χ(−1))`. Indeed
  `S(n)² = Σ_{ξ,η} χ(ξη) χ((ξ² − n)(η² − n))`. The inner sum over `n` is `p − 1` if `ξ² = η²` and `−1`
  otherwise (Lemma Q, and `χ(c²) = 1` for `c ≠ 0`). So the total is
  `−(Σ_ξ χ(ξ))² + p Σ_{ξ≠0} (χ(ξ²) + χ(−ξ²)) = p(p − 1)(1 + χ(−1))`.
- If `p ≡ 3 (mod 4)`, then (3) gives `S ≡ 0`. If `p ≡ 1 (mod 4)`, then (1)–(3) give
  `((p − 1)/2)(S(1)² + S(g)²) = 2p(p − 1)` for a non-square `g`, so `S(1)² ≤ 4p`. ∎

For `p ≥ 29` we have `(p − 15)² > 4p`, so `|S(d̄²)| < p − 15` and `N ≥ 1`. This uses no square root:
`S² ≤ 4p < (p − 15)²` is integer arithmetic.

*Step 3 (small primes).* For `p ∈ {3, 5, 7, 11, 13, 17, 19, 23}`, Step 1 is checked over all
`d̄ ∈ 𝔽_p*` and all four pairs of classes `(α, β)`. This is a finite computation that Lean can run by
`decide` on `ZMod p`.

*Checks.*

- `t_fp_surj.py` verifies the `𝔽_p` statement of Step 1 for all odd `p < 400` and all `d̄`
  (13,808 pairs, 0 failures). Only 18 pairs, all with small `p`, need a torsion witness or the
  trivial class.
- `t_charsum.py` verifies, for `p < 600`, Lemma J in the exact form `S(n)² + S(gn)² = 4p` when
  `p ≡ 1 (mod 4)`, and `S ≡ 0` when `p ≡ 3 (mod 4)`.
- `t_charsum.py` also verifies, for `p < 200` and all `d̄`, the bound `8N ≥ p − 15 − |S(d̄²)|` and
  `N ≥ 1` for `p ≥ 29`. There were 0 failures.

*Why this matters.* The textbook proof of G2 goes through good reduction: `E(ℚ_p)/2E(ℚ_p) ≅ E(𝔽_p)/2E(𝔽_p)`
has order 4 and `δ` is injective. In Lean that needs the formal group or reduction of points, the
Kummer map as a homomorphism, and the halving lemma. A direct attack on `D_{a,b}(𝔽_p) ≠ ∅` needs the
Hasse–Weil bound. Chevalley–Warning does not apply, since the two quadrics in four variables have
degree sum `4`, which is not less than `4`. The route above needs only Lemma Q, Lemma J and Hensel's
lemma for `X² − u`. It is the reason G2 becomes a medium-sized task.
