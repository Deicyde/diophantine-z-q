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
