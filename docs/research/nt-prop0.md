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
- **The good primes need neither the group law nor the Hasse bound** (§2.3, new). Here sufficiency
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
- **Plan** (§4). About 2,500–4,000 lines in nine files, in three tiers. The first step, the
  square-class criterion for `ℚ_p` and the places `p | d`, would show that the case
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
`D_{a,b}` (STANDARD in substance, Silverman X.3; the exact statement there is UNCHECKED here).
The Lean definition is the same in both cases.

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

1. Proposition 0 (§2.7) gives a bijection `sols ≃ Sel₂(d)`, `σ ↦ (a(σ), b(σ))`. So
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
factorization argument on squarefree integers (`Int.squarefree_natAbs`, `Nat.prod_primeFactors_of_squarefree`).

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
    their difference `2d` is a unit. Whichever is a unit forces `v(b)` or `v(a) + v(b)` to be even,
    and with `v(a)` even this gives `v(b)` even. ∎

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
- (2) `S(0) = Σ χ(ξ³) = Σ χ(ξ) = 0`.
- (3) `Σ_{n∈𝔽_p} S(n)² = p(p − 1)(1 + χ(−1))`. Indeed
  `S(n)² = Σ_{ξ,η} χ(ξη) χ((ξ² − n)(η² − n))`. The inner sum over `n` is `p − 1` if `ξ² = η²` and `−1`
  otherwise (Lemma Q, and `χ(c²) = 1` for `c ≠ 0`). So the total is
  `−(Σ_ξ χ(ξ))² + p Σ_{ξ≠0} (χ(ξ²) + χ(−ξ²)) = p(p − 1)(1 + χ(−1))`.
- If `p ≡ 3 (mod 4)`, then (3) gives `S ≡ 0`. If `p ≡ 1 (mod 4)`, then (1)–(3) give
  `((p − 1)/2)(S(1)² + S(g)²) = 2p(p − 1)` for a non-square `g`, so `S(1)² ≤ 4p`. ∎

For `p ≥ 29` we have `(p − 15)² > 4p`, so `|S(d̄²)| < p − 15` and `N ≥ 1`. This uses no square root:
`S² ≤ 4p < (p − 15)²` is integer arithmetic.

*Step 3 (small primes).* For `p ∈ {3, 5, 7, 11, 13, 17, 19, 23}`, Step 1 is checked over all
`d̄ ∈ 𝔽_p*` and all four pairs of classes `(α, β)`. This is a finite computation; in Lean it is best
done by a Boolean checker on `ℕ` run with `decide +kernel` (§4.2).

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

### 2.4 Odd primes dividing `d` (VERIFIED)

**Lemma B.** Let `p | d` be odd. Then `Loc_{ℚ_p}(a, b)` holds if and only if there are `i, j ∈ {0, 1}`
with `a d^i (−1)^j ∈ ℚ_p*²` and `b 2^i (−d)^j ∈ ℚ_p*²`. That is, `(a, b)` is one of the torsion classes
`(1, 1)`, `(d, 2)`, `(−1, −d)`, `(−d, −2d)`.

*Proof.*

- (⇐) By (Inv), it suffices to give witnesses for the four torsion classes: the first alternative
  for `(1, 1)`, and `x = d`, `0`, `−d` for the other three.
- (⇒) The first alternative and the torsion witnesses are covered by (Tor). Otherwise, let
  `k = v_p(x)`.
  - *`k ≤ 0`.* Then `|d/x| < 1`, so `x − d ≡ x` and `x + d ≡ x` by (P). Hence `b ≡ a` and `ab ≡ a`, so
    `b ≡ 1` and `a ≡ 1`.
  - *`k ≥ 2`.* Then `|x/d| < 1`, so `x − d ≡ −d` and `x + d ≡ d`. Hence `b ≡ −d` and `ab ≡ d`, so
    `a ≡ −1`. This is `(−1, −d)`.
  - *`k = 1`.* Write `x = dt` with `t` a unit. Then `x(x − d)(x + d) = d³ t(t − 1)(t + 1)`.
    - If `t ∓ 1` are both units, the valuation is 3, which is odd: impossible. They are not both
      non-units, since their difference is 2.
    - If `p | t − 1`, then `t ≡ 1` and `(t + 1)/2 ≡ 1` by (P). So `x ≡ d` and `x + d ≡ 2d`, giving
      `(a, b) ≡ (d, 2)`.
    - If `p | t + 1`, then `x ≡ −d` and `x − d = d(t − 1) ≡ −2d`, giving `(−d, −2d)`. ∎

The proof uses only (P), (Inv), (Tor) and valuations. The residue symbols enter only in §2.6, when
the class condition is turned into bits. This agrees with rv-slot-k-descent §1.2: the local image is
the span of the torsion images, of dimension 2.

### 2.5 The place 2, for `d ≡ 5 (mod 8)` (VERIFIED)

**Lemma T.** Let `d ≡ 5 (mod 8)`. Then `Loc_{ℚ₂}(a, b)` holds if and only if there are `i, j, k ∈ {0, 1}`
with `a d^i (−1)^j ∈ ℚ₂*²` and `b 2^i (−d)^j 5^k ∈ ℚ₂*²`.

The eight classes are the torsion classes and the products of each torsion class with `(1, 5)`.
Written with representatives in `{1, 3, 5, 7, 2, 6, 10, 14}`, they are `(1,1), (1,5), (7,7), (7,3),
(5,10), (5,2), (3,6), (3,14)`, which is the list of descent-alt §4.1 and the table of
rv-slot-k-descent §1.4.

*Proof of (⇐).* By (Inv) it suffices to treat one representative per class. The table gives a witness
for each:

| `(i, j, k)` | `(a, b)` | witness `x` | `x/a` | `(x − d)/b` | `(x + d)/(ab)` |
| --- | --- | --- | --- | --- | --- |
| `(0,0,0)` | `(1, 1)` | first alternative | | | |
| `(1,0,0)` | `(d, 2)` | `d` | `1` | `0` | `1` |
| `(0,1,0)` | `(−1, −d)` | `0` | `0` | `1` | `1` |
| `(1,1,0)` | `(−d, −2d)` | `−d` | `1` | `1` | `0` |
| `(0,0,1)` | `(1, 5)` | `1/4` | `1/4` | `(1 − 4d)/20` | `(1 + 4d)/20` |
| `(1,0,1)` | `(d, 10)` | `d(1+4d)/(1−4d)` | `(1+4d)/(1−4d)` | `(2d)²/(5(1−4d))` | `1/(5(1−4d))` |
| `(0,1,1)` | `(−1, −5d)` | `−4d²` | `(2d)²` | `(1+4d)/5` | `(1−4d)/5` |
| `(1,1,1)` | `(−d, −10d)` | `−d(1−4d)/(1+4d)` | `(1−4d)/(1+4d)` | `1/(5(1+4d))` | `2²/(5(1+4d))` |

Since `d` is odd, `1 ± 4d ≡ 5 (mod 8)`. So `(1 ± 4d)/5`, `(1 + 4d)/(1 − 4d)`, `(1 − 4d)/(1 + 4d)` and
`5(1 ± 4d)` are 2-adic units `≡ 1 (mod 8)`. Every entry of the last three columns is therefore an
even power of 2 times such a unit, and a square by (RT).

- The `(a, b)` column and the three quotients were checked by computer algebra
  (`t_witness_sympy.py`, below).
- `t_two_adic.py` checks that the four non-torsion points have the classes `(1,5), (7,7), (5,10),
  (3,14)` for 13 values `d ≡ 5 (mod 8)`.
- The witnesses are the points `x = 1/4` (slot-k §2.1, rv-slot-k-descent §1.4) and its translates by
  `T₁`, `T₂`, `T₃`, namely `x ↦ −d²/x`, `x ↦ d(x + d)/(x − d)` and `x ↦ −d(x − d)/(x + d)`. Lean
  needs only the rational numbers in the table, not the group law.

*Proof of (⇒).* By (Tor), assume `x ∉ {0, ±d}` with `x(x − d)(x + d)` a square, and let `v = v₂(x)`.

- *`v < 0` odd, or `v > 0` odd.* The valuation of `x(x − d)(x + d)` is `3v` or `v`, which is odd:
  impossible.
- *`v ≤ −4`.* `|d/x| ≤ 2⁻⁴`, so `x ± d ≡ x` by (P), and `(a, b) ≡ (1, 1)` as in §2.4.
- *`v = −2`.* Write `x = u/4`. Then `(x ∓ d)/x = 1 ∓ 4d/u ≡ 5 (mod 8)`, so `x ∓ d ≡ 5x`. The product
  is `≡ 25x³ ≡ x`, a square. So `a ≡ 1` and `b ≡ 5`.
- *`v ≥ 4`.* `x − d ≡ −d` and `x + d ≡ d` by (P), giving `(−1, −d)`.
- *`v = 2`.* `(x − d)/(−d) = 1 − x/d ≡ 5` and `(x + d)/d ≡ 5`. So `b ≡ −5d`, `ab ≡ 5d`, and
  `a ≡ −1`. This is `(−1, −5d)`.
- *`v = 0`.* Then `x − d` and `x + d` are even, and their sum `2x` has valuation 1. So one of them
  has valuation exactly 1. The other has valuation at least 2, and in fact odd and at least 3,
  because the product is a square.
  - If `v(x + d) ≥ 3`, then `x ≡ −d (mod 8)`, so `a ≡ x ≡ −d`. Also `b ≡ x − d = 2s` with
    `s ≡ −d (mod 4)`, so `b ≡ −2d` or `−10d`.
  - If `v(x − d) ≥ 3`, then `a ≡ d`. Also `ab ≡ x + d = 2s′` with `s′ ≡ d (mod 4)`, so `ab ≡ 2d` or `10d`,
    and `b ≡ 2` or `10`. ∎

Every step reduces to "a 2-adic unit `≡ 1 (mod 8)` is a square" and to residues mod 8. The proof is
longer than at `p | d` but has the same shape. The sampled image in `t_two_adic.py` (rational
`x = 2^k u` with `|k| ≤ 6`, `u < 2¹²`, on 6 curves) is exactly these eight classes.

### 2.6 From classes to the system `Σ(𝒞_d)` (VERIFIED)

Let `a = a(σ)` and `b = b(σ)` as in §0, and let `d ≡ 5 (mod 8)`.

**At `p ∈ S`.** By Lemma B and SQ(c), local solubility holds if and only if there are `i, j` with the
following properties.

- Valuations: `u_p + i` and `v_p + j` are even, so `i = u_p` and `j = v_p`.
- Residues: the unit parts of `a d^{u_p}(−1)^{v_p}` and `b 2^{u_p}(−d)^{v_p}` are squares mod `p`.

Since the residue bit is additive (`legBit` multiplicativity, `RouteK/Slots/Symbols.lean`), the bit
of the unit part of `a` at `p` is `a₀λ_p + a₁μ_p + Σ_{y≠p} u_y[y/p]`, and that of `d/p` is
`Σ_{y≠p}[y/p]`. The two residue conditions are then

```
a₀λ_p + a₁μ_p + Σ_{y≠p} u_y[y/p] + u_p Σ_{y≠p}[y/p] + v_p λ_p = 0,
b₀λ_p + b₁μ_p + Σ_{y≠p} v_y[y/p] + u_p μ_p + v_p (λ_p + Σ_{y≠p}[y/p]) = 0.
```

These are `E1_p` and `E2_p` of `Selmer.lean` (with `(Ku)_p = Σ_{y≠p}[y/p](u_y + u_p)`), the same
computation as rv-slot-k-descent §1.2.

**At `∞`.** Lemma ∞ gives `a₀ = b₀`, which is `(R)`.

**At `2`.** Write the class of an odd residue `w` mod 8 as `(ε, ω) = (lam8 w, mu8 w)`. These are the
homomorphisms `lam8`, `mu8` of `RouteK/System/Config.lean`, with `lam8_prod` and `mu8_prod`. The
relevant values are:

- `ε(−1) = 1`, `ω(−1) = 0`;
- `ε(5) = 0`, `ω(5) = 1`;
- `ε(d) = 0`, `ω(d) = 1`, since `d ≡ 5`;
- `ε(p) = λ_p`, `ω(p) = μ_p` for `p ∈ S`.

By Lemma T and SQ(b),(c), local solubility holds if and only if there are `i, j, k` with:

- valuations: `a₁ = 0` (since `d` is odd) and `b₁ = i`;
- `ε`, unit part of `a`: `a₀ + λ·u + j = 0`;
- `ω`, unit part of `a`: `μ·u + i = 0`;
- `ε`, unit part of `b`: `b₀ + λ·v + j = 0`;
- `ω`, unit part of `b`: `μ·v + j + k = 0`.

Eliminating `i = b₁`, `j = a₀ + λ·u` and `k` (which is free) leaves `a₁ = 0`, `b₁ = μ·u` and
`a₀ + λ·u = b₀ + λ·v`. Together with `(R)` this is `twoAdicRows 5`: `a1 = 0 ∧ b1 = mu ∧ lv = lu`. In
`Config.D` the class is `prodClass = Π_p (p mod 8) = d mod 8`.

**At `p ∉ S ∪ {2}`.** `a(σ)` and `b(σ)` are units, so Lemma G2 gives local solubility with no
condition.

### 2.7 Proposition 0 and the count (VERIFIED on paper)

**Proposition 0 (Lean form).** Let `d > 0` be squarefree with `d ≡ 5 (mod 8)`, and let
`σ : Unknowns d.primeFactors`. Then `(natConfig d _).IsSol σ ⟺ (a(σ), b(σ)) ∈ Sel2 d`.

*Proof.* `a(σ)` and `b(σ)` are squarefree. Combine §2.6 at `∞`, at `p ∈ S`, at `2`, and Lemma G2 at the
remaining primes. ∎

**Corollary (count).** `σ ↦ (a(σ), b(σ))` is a bijection `sols → Sel2 d`. In particular
`(Sel2 d).ncard = (natConfig d _).sols.card`.

*Proof.*

- Injective: the sign, `v₂` and `v_p` recover `a₀, a₁, u_p` and `b₀, b₁, v_p`.
- Onto: let `(a, b) ∈ Sel2 d`. By Lemma G1 and squarefreeness, no prime outside `S ∪ {2}` divides `a`
  or `b`. So `a = ±2^{a₁}Π_{p∈S} p^{u_p}` with exponents in `{0, 1}`, and likewise for `b`. Hence
  `(a, b) = (a(σ), b(σ))` for the `σ` read off from them, and `σ` is a solution by Proposition 0. ∎

*End-to-end check.* `t_prop0.py` implements the local conditions independently: classes of sampled
`ℚ_p`-points together with the torsion points, at `∞`, at `2` and at `p | d`. It compares them with
its own implementation of `E1`, `E2`, `(R)` and `(D)` for `c = 5` on 30 random `d ≡ 5 (mod 8)` with up
to 4 primes below 60 (a few values repeat), over every pair in the box `⟨−1, 2, p | d⟩²`. Result:
40,512 pairs, 0 mismatches. The same identification was checked before against an exact descent
(descent-alt §4.1: 600 values of `d`; rv-slot-k-descent §4.1) and against the Lean definitions
(cr3-check: 40 values of `d`). The new content here is the x-form of the coverings and the proofs
written in the order Lean needs.

## 3. What Mathlib v4.35.0 has (VERIFIED by grep, rev `56a0058`)

The full list, with line numbers, is in `scratch/nt-prop0/mathlib-inventory.md`. `M/` stands for
`Mathlib/`. The declarations this plan relies on were rechecked by hand: `hensels_lemma`,
`unitCoeff_spec`, `toZMod`, `jacobiSum`, `jacobiSum_nontrivial_inv`, `quadraticChar_sum_zero`,
`Rat.isSquare_iff_even_factorization` and `Subgroup.index_range`.

| Need | Mathlib | Verdict |
| --- | --- | --- |
| `ℚ_p`, `ℤ_p`, valuation, unit part | `Padic`, `PadicInt`, `Padic.valuation`, `valuation_ratCast`, `PadicInt.unitCoeff_spec` (`Padics/PadicIntegers.lean:432`), `mkUnits` | EXISTS |
| residue maps | `PadicInt.toZMod` (`Padics/RingHoms.lean:301`), `ker_toZMod` (328), `toZModPow` (448) | EXISTS |
| Hensel | `hensels_lemma` (`Padics/Hensel.lean:460`), hypothesis `‖F(a)‖ < ‖F′(a)‖²`; also `IsAdicComplete.henselianRing` | EXISTS |
| squares in `ℚ_p` (SQ, P, RT) | none; only `Rat.isSquare_iff_even_factorization` (`PadicVal/Basic.lean:394`) | MISSING (short) |
| squares in `ℝ` | `Real.isSquare_iff` | EXISTS |
| Legendre, Jacobi, `χ₄`, `χ₈`, reciprocity | `legendreSym.*`, `jacobiSym.*`, `ZMod.χ₄`, `ZMod.χ₈`; the repo's `legBit` layer (`RouteK/Slots/Symbols.lean`) | EXISTS |
| quadratic character sums | `quadraticChar`, `quadraticChar_sum_zero` (`QuadraticChar/Basic.lean:238`), `jacobiSum` (`JacobiSum/Basic.lean:48`), `jacobiSum_nontrivial_inv` (140) | PARTIAL: Lemma Q and Lemma J missing |
| Hilbert symbol, isotropy over `ℚ_p` or `𝔽_q`, conics | none | MISSING (not needed) |
| Chevalley–Warning | `char_dvd_card_solutions_of_sum_lt` (`FieldTheory/ChevalleyWarning.lean:110`) | EXISTS (not applicable to `D_{a,b}`) |
| Weierstrass curves, group law, base change of points | `WeierstrassCurve.Affine.Point`, `AddCommGroup` (`Affine/Point.lean:805`, needs `[Field F] [DecidableEq F]`), `Point.map`, `Point.baseChange` (822, 858) | EXISTS (not needed for Prop 0) |
| Kummer map, 2-descent, coverings, Selmer group of a curve | none in Mathlib. `IsDedekindDomain.selmerGroup` is `K(S, n)`, definition only. The repo's `Model/Descent/Kummer.lean` has `SqClass`, `sqc`, the 2-isogeny Kummer map `kummer` on `y² = x³ + bx` with `kummer_add`, `kummer_eq_one_iff`, `rescale_phi_phi` | MISSING in Mathlib, partial in the repo |
| `E(𝔽_q)` finite, Hasse bound, reduction of points over `ℚ_p` | none | MISSING (avoided by §2.3) |
| `[G : 2G] = #G[2]`, descent theorem, heights | `Subgroup.index_range` (`GroupTheory/Index.lean:902`), `AddCommGroup.fg_of_descent'` (`GroupTheory/Descent.lean:147`), `approx_parallelogram_law`, `finite_torsion` (`NumberTheory/Height/EllipticCurve.lean:80, 123`) | EXISTS (only for route R3) |

Two observations follow.

- **The repo's curve is already `C_d`.** `shortCurve (−d²)` is `y² = x³ − d²x`, so the repo's `kummer`
  is the first coordinate `δ₁` of `δ`, as a homomorphism over any field. This matters only for route
  R3 (§5), which needs the group law.
- **Nothing missing is deep.** Everything Proposition 0 needs from outside the repo is short: SQ,
  (P), (RT), Lemma Q and Lemma J. The integer congruence lemmas `realChar_exists_sq_mod_pow_odd` and
  `realChar_exists_sq_mod_two_pow` (`Progressions/RealChar/Hensel.lean`) are not usable as stated,
  because they concern `ℤ/pⁿ`, not `ℚ_p`. `hensels_lemma` gives SQ directly.

## 4. A Lean plan

### 4.1 Files and statements, in dependency order

The new code would live in a directory such as `ZInQKernel/RouteK/Selmer/`. It imports
`RouteK/System` (for `Config`, `IsSol`, `natConfig`, `natClass`), `RouteK/Slots/Symbols.lean` (for
`legBit`) and the Mathlib modules of §3. All statement names below are proposals (SPECULATIVE until
written).

1. **`Covering.lean`** (§1).
   - `Loc K d a b`, with `loc_congr_sq` (Inv) and `loc_torsion` (Tor);
   - the projective covering and `cov_iff_loc`, plus the Kummer-image form `loc_iff_kummer` (Lemma 1.2);
   - `Sel2 d` and `CertifiedRankSel`;
   - `certifiedRank_of_sel : CertifiedRankSel → Prop0Statement → CertifiedRank`, the argument of §1.4
     steps 2–5, with Proposition 0 still a hypothesis at this stage.

   This makes the reduction explicit before any local work is done.
2. **`PadicSquare.lean`** (§2.1).
   - `isSquare_padic_iff` (SQ(a), SQ(c)) and `isSquare_two_adic_iff` (SQ(b), SQ(c)) for `x : ℚ_[p]`, with the
     unit part taken from `Padic.valuation` and `PadicInt.mkUnits`;
   - the perturbation lemmas (P) and the rational tests (RT).
   - The two Hensel halves are already proved in `scratch/nt-prop0/Probe.lean`.
3. **`Real.lean`**: Lemma ∞, `loc_real_iff : Loc ℝ d a b ↔ (0 < a ↔ 0 < b)`.
4. **`BadOdd.lean`**: Lemma B, `loc_padic_dvd_iff`, for odd `p | d` (§2.4).
5. **`Two.lean`**: Lemma T, `loc_two_adic_iff`, for `d ≡ 5 (mod 8)`. It has the eight witnesses of the
   table in §2.5 and the case analysis on `v₂(x)`.
6. **`CharSum.lean`**: everything over `𝔽_p`, with no `p`-adic content.
   - Lemma Q (proved in `scratch/nt-prop0/ProbeQ.lean`) and Lemma J;
   - the count `8N ≥ p − 15 − |S(d̄²)|`;
   - `exists_xi`, the statement of Step 1 of §2.3, for `p ≥ 29`, and for `p < 29` by a Boolean checker
     run with `decide +kernel`.
7. **`Good.lean`**: Lemma G1 (`loc_padic_good_even`) and Lemma G2 (`loc_padic_good_of_units`), the lift
   from `CharSum.lean` by SQ(a).
8. **`Bits.lean`** (§2.6).
   - Turn the class conditions into `E1_p`, `E2_p`, `(R)` and `twoAdicRows 5`.
   - Residue bits of `a(σ)` and `b(σ)` at `p ∈ S` through `legBit` multiplicativity, and the mod-8
     characters through `lam8_prod` and `mu8_prod`.
9. **`Prop0.lean`** (§2.7).
   - `prop0 : (natConfig d _).IsSol σ ↔ (aOf σ, bOf σ) ∈ Sel2 d`;
   - `solsEquivSel2`, with `(Sel2 d).ncard = (natConfig d _).sols.card`;
   - `certifiedRank_of_certifiedRankSel : CertifiedRankSel → CertifiedRank`.

The main theorem then has a variant with `CertifiedRankSel` in place of `CertifiedRank`, as
`..._of_poleCompleteness` and `..._of_sixContactEstimate` are variants today.

### 4.2 The hardest steps

- **The case analyses over `ℚ_p` and `ℚ₂`** (files 4 and 5). They need a convenient interface:
  write `x = p^k u` with `u ∈ ℤ_p*`, then read the classes of `x ± d` off `k` and the residue of `u`
  (mod `p`, or mod 8 at 2). Lemma T has about ten cases. The risk is bookkeeping friction (norms versus
  valuations, casts from `ℤ` and `ℚ`), not mathematics. Proving (P) once in a reusable form (in the
  shape "`|y| < |x|` implies `x + y ≡ x`") keeps every case to a few lines.
- **Lemma J** (file 6). Exchanging the order of the triple sum `Σ_n Σ_{ξ,η}` and splitting
  `ξ² = η²` from `ξ² ≠ η²` is routine on paper and tedious with `Finset` sums. The square-class
  invariance `S(nt²) = χ(t)S(n)` needs a reindexing, like the substitution in `ProbeQ.lean`. The step
  from `Σ_{n≠0} S(n)²` to `((p − 1)/2)(S(1)² + S(g)²)` needs the fact that every nonzero square has exactly two square roots
  (`quadraticChar_card_sqrts`).
- **`Bits.lean`.** Products over `d.primeFactors` and the residue bit of a product of primes are of
  the same kind as the existing `Realize.lean` and `Slots/Symbols.lean`. They are long but follow known
  patterns.
- **Small primes.** The check for `p < 29` covers about 6,000 triples `(d̄, class, ξ)`. It should be
  a `Nat`-valued Boolean checker proved by `decide +kernel`, not `decide` on `ZMod p`, because the
  kernel evaluates `ZMod` arithmetic and `Decidable` instances slowly. Alternatively one could improve the constant 15, but this is not
  needed.

### 4.3 Effort tiers (SPECULATIVE estimates)

| Tier | Content | Size |
| --- | --- | --- |
| Cheap wins | files 1 and 3; the Hensel halves of file 2 (done: `Probe.lean`); Lemma Q (done: `ProbeQ.lean`) | 300–500 lines, days |
| Medium investment | file 2 complete; files 4, 6, 7, 8, 9 | 1,500–2,500 lines, 2–4 weeks |
| Bigger investment | file 5 (Lemma T, necessity) and integration with `Main.lean`; separately, route R3 of §5 | 600–1,000 lines for file 5; R3 one to two months more |

Slot-k §4.3 estimated "months" for Proposition 0, assuming Galois cohomology and local images were
needed. With the coverings in x-form and the character-sum argument at the good primes, neither is
needed. The whole of Proposition 0 is an elementary development of about 2,500–4,000 lines.

### 4.4 The first step

**Test.** Write `PadicSquare.lean` (SQ(a), SQ(c), (P) for odd `p`) and `BadOdd.lean`, ending with

```lean
theorem loc_padic_dvd_iff {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {d : ℕ} (hpd : p ∣ d)
    (hd : Squarefree d) (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Loc ℚ_[p] d a b ↔ ∃ i j : ℕ, i < 2 ∧ j < 2 ∧
      IsSquare ((a * d ^ i * (-1) ^ j : ℤ) : ℚ_[p]) ∧ IsSquare ((b * 2 ^ i * (-d) ^ j : ℤ) : ℚ_[p])
```

**Success criterion.** Compiles with no `sorry`, `#print axioms` shows only the standard three, at
most about 600 lines, and no declaration takes more than 30 s. Success shows that a case analysis
over `ℚ_p` with valuations, unit parts and residues is manageable in Lean. Files 5 and 7 are the
same kind of argument (with residues mod 8, respectively a lift), so their cost can then be
extrapolated.

**Parallel probe.** Lemma J over `ZMod p`, in the form `(S 1)^2 ≤ 4p`, has no `p`-adic content and
can be done independently. Success criterion: at most about 300 lines.

The probes run so far: both Hensel halves of SQ (`Probe.lean`, about 75 lines) and Lemma Q
(`ProbeQ.lean`, about 35 lines, compiled on the first attempt) build against the project's Mathlib
with standard axioms only.

## 5. Routes and ranking

**R1. Proposition 0 in full; CR₃ replaced by `CR₃^Sel`** (§1.4, §2, §4).

- *Payoff.* The explicit system, Monsky's matrix and the Legendre-symbol bookkeeping leave the trust
  boundary. The hypothesis reads "for these `d`, Selmer rank 3 implies `Ш[2] = 0`", with `Sel₂` in its
  textbook form (§1.3). By Silverman X.1.4 this is equivalent to `rank C_d(ℚ) ≥ 1`, which is what Kriz,
  or TYZ with GZK, provide.
- *Main obstacle.* Volume and friction rather than mathematics: the 2-adic case analysis of Lemma T,
  Lemma J, and the bit bookkeeping of `Bits.lean`. Every step has a written elementary proof (§2), and
  the whole identification passed an independent end-to-end test (`t_prop0.py`, 40,512 pairs).
- *First test.* `loc_padic_dvd_iff` as in §4.4: at most about 600 lines, no `sorry`, standard axioms.
- *Chance: high.* Nothing in it is deep. The only analytic-looking input, at the good primes, is
  replaced by Lemma J, an orthogonality identity. Mathlib has every primitive (Hensel, residue maps,
  quadratic characters, Jacobi sums), and the two probes compiled with little effort.

**R3. The congruent-number form: hypothesis "`C_d(ℚ)` is infinite".**

> **CR₃^cong.** If `d ≡ 5 (mod 8)` is squarefree, `#Sel₂(d) = 8` and `Sel₂(d)` contains a pair with
> `|a| ≡ 7 (mod 8)`, then `C_d(ℚ)` is infinite, i.e. `d` is a congruent number.

Lean would then prove `CR₃^Sel` from `CR₃^cong`. On top of R1 this needs:

- (a) the pair map `δ` as a homomorphism on `C_d(ℚ)` with kernel `2C_d(ℚ)`. Its first coordinate is the
  repo's `kummer` on `shortCurve (−d²)`, with `kummer_add`; the kernel would come from
  `kummer_eq_one_iff` and `rescale_phi_phi`, or from a halving lemma;
- (b) `δ(C_d(ℚ)) ⊆ Sel₂(d)`, which is Lemma 1.2 over `ℚ` together with "rational squares are local
  squares";
- (c) Mordell–Weil for `C_d/ℚ`, from (a), (b) and `#Sel₂ = 8` (finite index of `2C_d(ℚ)`), via
  `AddCommGroup.fg_of_descent'` and Mathlib's naive height. This is the pattern of `mordellWeilE`;
- (d) for a finitely generated infinite `C_d(ℚ)` with `C_d(ℚ)[2]` of order 4, `[C_d(ℚ) : 2C_d(ℚ)] ≥ 8`,
  hence `δ(C_d(ℚ)) = Sel₂(d)`.

Assessment:

- *Payoff.* The deep input reads exactly as the conclusions of Tian–Yuan–Zhang ("`n` is a congruent
  number") or of any rank-one theorem. `Ш` and the injectivity half of Silverman X.1.4 also move into
  Lean.
- *Main obstacle.* Items (a), (c) and (d): the full 2-descent homomorphism (the repo only has the
  2-isogeny half, and `phi` has no `phi_add`), and Mordell–Weil over `ℚ` for a family of curves.
- *First test.* Define `δ₂` (the class of `x − d`) on `shortCurve (−d²)` over any field and prove
  `δ₂(P + Q) = δ₂(P)δ₂(Q)`, reusing the proof of `kummer_add`. Success criterion: under 400 lines.
- *Chance: medium.* The pieces have precedents in the repo (MW over `ℚ(√2)`), but the work is about
  as large again as R1.

A variant keeps the explicit system as the antecedent ("`Σ(𝒞_d)` has 8 solutions, including class
`a`, ⇒ `C_d(ℚ)` infinite"). It then needs only the necessity half of Proposition 0, since rational
points give solutions, and not Lemma G2 or the sufficiency half of Lemma T. Its hypothesis is less
canonical, because the antecedent is still the system.

**R2. Proposition 0 at the bad places only** (a milestone of R1, and its fallback).

- *Payoff.* Define `Sel₂^S(d)` with conditions at `∞`, `2` and `p | d` only, on the box `ℚ(S ∪ {2}, 2)²`, and
  skip §2.3. The trust statement then adds one STANDARD fact: at a prime of good reduction not
  dividing 2, the local image is the unramified subgroup (Silverman X.4; exact proposition number
  UNCHECKED here).
- *Main obstacle.* As R1, minus files 6 and 7.
- *First test.* As R1.
- *Chance: high*, but the payoff is strictly smaller than R1's. Since §2.3 turned out elementary, R2
  is worth doing only as an intermediate commit.

**Rejected approaches** (low chance or no benefit):

- Hilbert symbols: the local conditions could be written as Hilbert-symbol identities, but Mathlib
  has none, and the x-form makes them unnecessary.
- At the good primes, the textbook route through `E(ℚ_p)/2E(ℚ_p) ≅ E(𝔽_p)/2E(𝔽_p)`: it needs reduction
  of points over `ℚ_p`, the formal group and the Kummer homomorphism.
- At the good primes, the Hasse–Weil bound for `D_{a,b}/𝔽_p`, or Chevalley–Warning: the latter does not
  apply (degree sum 4, four variables).
- Galois cohomology: it is not needed (§1.3).

| Rank | Route | Payoff | Main obstacle | First test | Chance |
| --- | --- | --- | --- | --- | --- |
| 1 | R1: full Proposition 0, `CR₃^Sel` | system out of the trust boundary; hypothesis = textbook `Sel₂` + "Selmer rank 3 ⇒ `Ш[2]=0`" | Lemma T, Lemma J, bit bookkeeping (2,500–4,000 lines) | `loc_padic_dvd_iff` in ≤ 600 lines | high: all steps elementary, written and tested; two probes compiled |
| 2 | R3: `CR₃^cong` ("`d` is congruent") | hypothesis in the exact form of TYZ / rank-one theorems | full 2-descent homomorphism, MW over `ℚ` for `C_d` | `δ₂` additive, ≤ 400 lines | medium: precedent in the repo, but as large again as R1 |
| 3 | R2: bad places only | as R1, plus one cited STANDARD fact | as R1 minus files 6–7 | as R1 | high, but dominated by R1 |
