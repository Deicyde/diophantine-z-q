# Route K for pole completeness: an adversarial check

This note checks "Route K" of `docs/research/rs-pole.md` (§4.1) independently. Route K changes
the pole polynomial `Q_pole` so that its two curves are congruent number curves
`C_ℓ : y² = x³ − ℓ²x = x(x − ℓ)(x + ℓ)` instead of the curves `E_ℓ : y² = x(x − ℓ)(x + 3ℓ)`.
It then proves pole completeness (PC) from Kriz's 2-converse for congruent number curves instead of
the manuscript's restricted converse RC (Theorem 5.3, line 1005, whose proof runs through
Sections 7–9 and Appendices E–G).

Every claim carries one of three marks.

- **VERIFIED**: checked against the manuscript, the Lean sources or the source text, or by an
  exact computation. Scripts are in `scratch/rv-route-k/` and are independent of
  `scratch/rs-pole/`.
- **STANDARD**: a published theorem, with a reference.
- **SPECULATIVE**: an idea or expectation that is not proved.

Notation. `Q_pole^C` is `Q_pole` with `T₁ = A(A − e)(A + e)` and
`T₂ = A(Az² − eH)(Az² + eH)`. `Φ_C(B)` is its rational solubility. For a signed divisor `m` of
2730, put `β = sqf(mB)` and `θ = sqf(m(m − B))`, where `sqf` is the signed squarefree part.
The Kummer map of `C_d` is `P ↦ (x, x − d) ∈ (ℚ*/ℚ*²)²`. The *first coordinate* of a class is
the class of its abscissa.

## Verdict

**Route K holds with repairs.** No counterexample was found, and the deep input fits. The route
is not yet a proof, because one elementary but essential lemma is missing.

What survives the check:

- Soundness carries over verbatim; with `x + ℓ` the cubic step even holds at `p = 3` (§4.1).
- The reformulation of `Φ` by two parameters, adapted to `C_ℓ`, is correct (§4.2).
- Kriz's theorem states what Route K needs, for every congruent number curve (§4.3).
- No Lean statement other than `polePoly` and its template has to change, and the variable count
  of the frozen target is kept exactly (§4.5).

The repairs:

1. **The descent lemma must be proved** (the gap; §4.4).

   > For every admissible `B` there is a signed divisor `m` of 2730 and a squarefree `n` with
   > `β | n` such that each of `C_n` and `C_{nθ}` either carries the 2-torsion point with
   > abscissa class `β` or has `dim Sel₂ = 3` with a class of first coordinate `β`.

   Experiments support it:

   - all 60 inputs run with every multiplier allowed were solved: 30 random, 30 adversarial;
   - every fixed `(B, m)` pair retried with the larger search was solved: 8 stress pairs, and 10
     inputs with `m = 1` fixed and `θ` built from 4–9 small primes;
   - all 60 inputs run with the TYZ certificate were solved.

   Suitable auxiliary products can be rare: for some `(β, θ)` the class `β` lies on `C_{nθ}`
   for only a fraction of order `2^{−ω(θ)}` of random `n'`. So the proof must choose the
   Legendre symbols of the auxiliary primes, as the manuscript does for `E_ℓ`.
2. **The deep input.**
   - Kriz's theorem is an unrefereed preprint (arXiv:2002.04767v5, 19 Oct 2022; no journal
     reference on arXiv, and I found no publication). Trust moves from the manuscript's
     8,000 lines to Kriz's 214-page preprint.
   - **A published alternative works in the experiments.** Tian–Yuan–Zhang (Asian J. Math.
     2017), in Smith's determinant form, certifies rank one for a curve with one extra
     linear condition. Requiring it on every curve that needs the converse, the descent still
     succeeded on 60 of 60 inputs (§4.3, §4.4).
3. **Small corrections to the source note.** Its explicit `θ = 1` witness is wrong (§4.2).
   Its reformulation must be redone for `C_ℓ`: the parametrization and the surface change (§4.2).
   The "abscissa class `β`" condition needs the torsion bookkeeping of §4.2, and the cases
   `β ≡ ±1` need care.
4. **Lean and construction changes**: four definitions, a copy of upstream's 330-line valuation
   lemma with `3` replaced by `1`, two parity lemmas, and the external JavaScript construction
   (§4.5).

The ranking and the recommendation are in §5.

## 1. The statement and every use

### 1.1 Statement (VERIFIED)

- Manuscript Theorem 5.2 (`hyp:PC`, lines 1001–1003): for rational `B` with square reduced
  denominator, `0 < B < 1/2` and `v_p(B) ≥ 4` for `p ∈ S₀ = {2, 3, 5, 7, 13}`, `Φ(B)` holds.
- Lean `ZInQ.PoleCompleteness` (`ZInQKernel/Hypotheses/Pole.lean`) states it for
  `ZInQ.PoleSoluble`, the solubility of `ZInQ.polePoly`.
- `Q_pole` is defined at lines 975–987. In Lean it appears twice:
  - as `polePoly` (the rational function in the hypothesis);
  - as the template polynomial `polePolyOf`, built from `poleM`, `poleH`, `poleT1` and `poleT2`
    (`Syntax/Templates/Core.lean`, lines 230–330), with `ev_polePolyX` linking the two.

### 1.2 Uses in Lean (VERIFIED by `grep -rn hPC ZInQKernel`)

The completeness direction applies PC exactly twice:

| Site | Input `B` |
| --- | --- |
| `Multiplication/Completeness/SlopeCompleteness.lean:187` (`ZInQ.Mult.slope_complete`) | `slopeR ℓ a R₀ / Θ²`, hypotheses from `pole_input_valuations` and `pole_input_small` |
| `Assembly/Local/TestCompleteness.lean:104` (`ZInQ.Assembly.test_complete`) | `testB …`, hypotheses from `poleInput_local` and `poleInput_real` |

Every other occurrence of `hPC` only passes it along: `completeness_core`, `multiply_complete`,
`multiplication_exact`, `value_relation_iff_of`, `Pstar_spec` and `assembly`.

The soundness direction never uses PC. It uses only the obstruction lemma:

- `ZInQ.Mult.pole_obstruction` (`Multiplication/Certificate/Parity.lean`), consumed at
  `Multiplication/Soundness/CommonGroup.lean:114`;
- `ZInQ.Assembly.poleSoluble_no_negative_odd` (`Assembly/Local/PoleObstruction.lean`), consumed
  at `Assembly/Local/TestDivisibility.lean:231`.

Both reduce, through `poleSystem_of_polePoly_eq_zero`, to upstream's
`ZInQ.ValuationObstruction.poleSystem_no_negative_odd_valuation` (`lean/ZInQ/PoleValuation.lean`).
The lemma `abscissa_val_even` (`Parity.lean`) has no consumer outside its file.

### 1.3 Uses in the manuscript (VERIFIED)

- Completeness: line 1751 (multiplication) and line 6233 (Lemma 11.2).
- Soundness, via Lemma 5.1 only: lines 1196 and 6167.
- Lemma 1.2: line 101.
- The curves `E_ℓ`, the factor `x + 3ℓ`, the class `ℓ ≡ 11 (mod 12)` and `j = 35152/9` occur
  outside Sections 7–9 and Appendices E–G only at lines 979, 986, 1006–1012 and 1058, all inside
  Section 5.
- A label scan shows that the only references from outside into Sections 7–9 or Appendices E–G
  are the overview pointers at lines 126–127, 1015–1016 and 6597–6598 (`sec:rc`, `sec:limits`,
  `app:even-source`, `app:endpoints`). No result proved there is used anywhere else. Deleting RC
  therefore removes nothing that other parts of the proof need.

## 2. The weakest form the proof needs

### 2.1 What the call sites need (VERIFIED)

Each call site needs `Φ(B)` for one input `B = R₀s(q)²`. The square class `R₀ℚ*²` is fixed by
the instance, and `s` depends on a witness `q` chosen by weak approximation. This agrees with
`rs-pole.md` §2.1. The call sites supply more than PC asks: `v_p ≥ 6` at odd `p ∈ S₀` in the
test, and `v_p ≥ 103C_p + 8` on `S_b` in multiplication. Nothing is gained from this extra
strength, because the descent only uses that `1 − B/m` is a square at the primes of `S₀`.

### 2.2 What Route K needs (VERIFIED)

Route K keeps PC's statement and changes only the polynomial. The Lean hypothesis would be
`PoleCompleteness_C`: the same quantifiers, with `polePoly` replaced by its `x + ℓ` version.

The proof of `Φ_C(B)` uses, per input:

- one multiplier `m` out of the 64 signed divisors of 2730 (the six bits `b₀, …, b₅` realize
  every signed divisor);
- two curves, `C_n` and `C_{nθ}`;
- the 2-converse for at most those two curves, and for only one of them when `n = ±β` (§4.4).

So the needed external statement is much weaker than a universal converse:

> **K∃.** For every admissible `B` there are `m` and `n` such that `C_n` and `C_{nθ}` each have a
> rational point with abscissa in `βℚ*²`.

Kriz's theorem is used only on curves `C_d` with `dim Sel₂(C_d) = 3`, and only in the form
"`corank Sel_{2^∞} = 1` implies `rank = 1`".

## 3. The manuscript's proof and its trust leaves

The proof of PC from RC is at lines 1019–1121:

1. squareclass bookkeeping with the multipliers (real, 2-adic and 3-adic signatures);
2. a Rédei-matrix construction of `n ≡ 11 (mod 12)` with auxiliary prime slots, so that `E_n`
   and `E_{nθ}` have `dim Sel₂ = 3` and contain the Kummer class `(β, 1)`;
3. the corank lemma (line 1072, Poonen–Stoll, record A019);
4. RC, applied twice;
5. the forward lemma (line 1086: BCDT, Kolyvagin and Kato; records A020, A066 and A082);
6. rescaling to the eleven witnesses.

RC itself occupies Sections 7–9 and Appendices E–G (lines 1760–5745 and 6825–10935).

Classifying the anchored sites of `docs/theorem-application-audit/application-sites.json` by
manuscript region (VERIFIED, script below):

- **39 records occur only inside the RC proof**: A022–A045, A049–A054, A067–A070, A073–A075,
  A080 and A081. They cover:
  - Selmer parity, Kato's Euler system, and nonvanishing (Hoffstein–Luo, Bump–Friedberg–Hoffstein);
  - explicit Gross–Zagier, oriented supersingular reduction, Waldspurger, Carayol;
  - Serre's open image, Heegner norm relations, and the Nekovář–Milne duality package;
  - Weil representation and theta modularity, Chebotarev, class field theory;
  - auxiliary inputs.
- **Shared with Section 5**: A020 (forward rank one), A057 (Dirichlet), A065, A066 (modularity)
  and A082 (forward rank zero).
- **Only in Section 5**: A019 (Poonen–Stoll).

Beyond those published theorems, the leaves include roughly 8,000 lines of new, unrefereed
reasoning.

## 4. Route K, checked point by point

### 4.1 Soundness (VERIFIED)

Lemma 5.1 (lines 988–999), re-derived for `Q_pole^C`. Let `B ≠ 0`, let `Φ_C(B)` hold, and let
`p ∉ S₀` with `k = v_p(B) < 0` odd.

1. **Valuations of `A` and `H`.** `m` is a signed divisor of `2730 = 2·3·5·7·13`, so `p ∤ m`
   and `v_p(A) = k`. Since `2k < k`, `v_p(A − B²) = 2k` and `v_p(H) = 3k`, which is odd.
2. **Nonvanishing.** The equation `eHzw = 1` gives `e, H, z ≠ 0`.
3. **Choice of curve.** Exactly one of `e`, `eH` has even valuation. Call it `ℓ` and its point's
   abscissa `x`, so `x = A` or `x = Az²`; then `v_p(x) = k + 2v_p(z)` is odd.
   - Here `(Az², zr₂)` lies on `C_{eH}` because `(zr₂)² = z²T₂ = Az²(Az² − eH)(Az² + eH)`.
     The same identity holds with `+3eH`.
4. **Scaling.** `(x, y, ℓ) ↦ (p^{−2a}x, p^{−3a}y, p^{−2a}ℓ)` makes `ℓ` a unit and keeps
   `v_p(x)` odd.
5. **The cubic.**
   - If `v(x) > 0`, then `v(x − ℓ) = v(x + ℓ) = 0`, so `v(x(x − ℓ)(x + ℓ)) = v(x)`. This holds
     for every prime `p`. For `x + 3ℓ` it needs `p ≠ 3`; that is the only place where the
     factor 3 enters.
   - If `v(x) < 0`, the valuation is `3v(x)`.
   - The cubic is nonzero, because `v(x)` is odd, so `x ∉ {0, ℓ, −ℓ}`.
6. **Contradiction.** The cubic is a square `y²` of odd valuation, which is impossible.

Consequences:

- The lemma holds for `Q_pole^C` with the same `S₀`. `S₀` is now needed only because of the
  multipliers.
- The congruence `ℓ ≡ 11 (mod 12)` and `j = 35152/9` play no role in soundness. In the
  manuscript they are used only in RC and its descent (lines 1006–1016, 1058).
- The Lean proof transfers. Upstream `curve_rhs_nonzero_and_valuation` and
  `poleSystem_no_negative_odd_valuation` (`lean/ZInQ/PoleValuation.lean`, with `hp3 : p ≠ 3`
  and `hv3l`) need a copy with `3·l` replaced by `l`. The hypothesis `p ≠ 3` and the step
  `v_p(3l) = v_p(l)` disappear.

### 4.2 The reformulation of `Φ` (VERIFIED, `reform_check.py`)

The source note's Proposition 1 is stated for `E_ℓ`. For `C_ℓ` the computation changes as
follows.

**Parametrization.** `C_ℓ` has a point with `x = β` exactly when `β² − ℓ² ∈ βℚ²`. This is a
conic in `(ℓ, w)` with rational point `(β, 0)`. Its lines give

```
ℓ(τ) = β(β − τ²)/(β + τ²),    y(τ) = 2β²τ/(β + τ²),    τ ∈ ℙ¹(ℚ),
```

with `τ = ∞` corresponding to the torsion point `(β, 0)` on `C_{−β} = C_β`. The inverse is
`τ = y/(β + ℓ)`. Modulo squares `ℓ(τ) ≡ g(τ) := β(β² − τ⁴)`, and `g(β/τ) ≡ −g(τ)`. So the set
of `ℓ` is closed under sign, which matches `C_ℓ = C_{−ℓ}`.

**Reformulation.** For `B ≠ 0, m`, `Φ_C(B)` holds if and only if, for some signed divisor `m`
of 2730, there are `τ₁, τ₂ ∈ ℙ¹(ℚ)` with

```
θ · (β² − τ₁⁴)(β² − τ₂⁴) ∈ ±ℚ*².
```

This is a double cover of `ℙ¹ × ℙ¹` branched along a curve of bidegree `(4, 4)`. It is the
congruent-number analogue of the note's surface, not that surface itself.

**Checks.**

- The identity `y(τ)² = β(β − ℓ)(β + ℓ)` and the inverse map were checked on 455 rational
  `(β, τ)`. The note's `E_ℓ` formula `ℓ = β(βt² − 1)/(βt² + 3)` was checked on the same set.
- Forty explicit zeros of `Q_pole^C` were built from `(m, τ₁, τ₂)` with exact rational witnesses
  and checked to vanish in `ℚ`. Examples:
  - `B = 5/162`, `m = 2`, `θ = 319`, `(τ₁, τ₂) = (−2, −3/2)`;
  - `B = 80/121`, `m = 1`, `θ = 41`.

  These test the algebra only; such `B` are not admissible.

**"Only the abscissa class matters"** is correct: `Q_pole^C` constrains only
`T₁, T₂ ∈ ℚ²`, so the second Kummer coordinate is free. Two refinements are needed for the
descent.

- **Torsion bookkeeping.** The Kummer first coordinates of the torsion points are `d`, `−d` and
  `−1`, for `(d, 0)`, `(−d, 0)` and `(0, 0)`. But `(0, 0)` has abscissa `0`, which is not in
  `βℚ*²`. So a Selmer class with first coordinate `β ≡ −1`, or a trivial class (`β ≡ 1`), is
  realized by an affine point with abscissa in `βℚ*²` only through a non-torsion point (`P + T`
  or `2P`). That needs rank ≥ 1, unless `β ≡ ±d`. The search below certifies exactly:
  "`β ≡ ±d`" (the torsion point `(±d, 0)`), or "`dim Sel₂ = 3` and `β` is a first coordinate"
  (rank 1 by Kriz, so every class comes from a point and infinitely many points have it).
- **The `θ = 1` witness.** If `m(m − B) = c²`, then `H = B²c²`. The correct 2-torsion witness
  is `e = A`, `z = Bc`, `r₁ = r₂ = 0`, `w = (AHBc)⁻¹`, and it works for both polynomials. The
  note's `z = c`, `w = (A³c³)⁻¹` gives a nonzero value; for `B = 7/16`, `m = 1`, `c = 3/4` it is
  about `25.6`.

### 4.3 Kriz's theorem: statement, hypotheses, status

**Source.** D. Kriz, *Supersingular main conjectures, Sylvester's conjecture and Goldfeld's
conjecture*, arXiv:2002.04767v5 (19 Oct 2022, 214 pages). The text below was read in v5.

- **Theorem 1.1** (= Theorems 9.23 and 10.13). Let `E/ℚ` be an elliptic curve and `K/ℚ` an
  imaginary quadratic field such that `E/K` has CM by `O_K`, and let `p` be the unique prime
  ramified in `K`. Then the `p`-converse holds for `r = 0, 1`.
- **Theorem 10.13** (rank 1). Under these hypotheses,
  `corank_{ℤ_p} Sel_{p^∞}(E/ℚ) = 1 ⟹ r_an = r_alg = 1` and `#Ш(E/ℚ) < ∞`.
- **Theorem 9.23** (rank 0) is the analogue with corank 0.
- **Theorem 10.17(2).** For `E_d : y² = x³ − d²x`, if `r₂(E_d/ℚ) ≤ 1`, then
  `r_an = r_alg = r₂` and `#Ш < ∞`. The proof: "immediately follows from Theorems 9.23 and 10.13
  with `p = 2` and `K = ℚ(i)`".

Hypotheses, checked against the text (VERIFIED):

1. **CM by `O_K` over `K`.** `C_d` has `End_K = ℤ[i] = O_{ℚ(i)}` for every nonzero `d`, square
   or not, any sign, any parity. Since `C_d ≅ C_{dλ²}`, squarefreeness is immaterial.
2. **Only extra condition: `f₀ ≥ 4`** (Assumption 5.6(1), Example 5.7). Here `f₀²` is the
   prime-to-`p` part of the conductor. For `p = 2` the proofs of 9.23 and 10.13 treat `f₀ ≤ 3`
   by appeal to LMFDB data: "all elliptic curves with CM by `ℤ[i]` or `ℤ[√−2]` of conductor
   `≤ 3²·2⁸ = 2304`".
   - For `C_d` with `d` squarefree, `f₀` is the odd part of `|d|`. So `f₀ ≤ 3` only for
     `d ∈ {±1, ±2, ±3, ±6}`.
   - In Route K, `nθ` has an odd prime factor `≥ 11`, because `θ > 1` is prime to 2730.
   - `C_1`, `C_2` and `C_3` have `dim Sel₂ = 2` and are never used through the converse.
   - `C_6` has the explicit point `(−3, 9)`.
   - **So the LMFDB step is never needed** (VERIFIED, `validate_sel2.py`).
3. **Parity.** Theorem 10.13's proof imports root number −1 from "previous work on the parity
   conjecture" (Monsky; Dokchitser–Dokchitser). This is inside Kriz's proof and adds nothing to
   check.
4. **Congruence conditions.** There are none on `d`, and no conductor-exponent condition at 2.

**Status.** arXiv lists v1 (Feb 2020) to v5 (Oct 2022) with no journal reference. I found no
published version. It should be treated as a complete preprint by an expert, not as a refereed
theorem. Kriz's published monograph *Supersingular p-adic L-functions, Maass–Shimura operators and Waldspurger formulas* (Annals of Mathematics Studies, Princeton, 2021) is a different work.

**Fallback: Tian–Yuan–Zhang**, *Genus periods, genus points and congruent number problem*,
Asian J. Math. 21 (2017), no. 4, 721–773 (published; read in arXiv:1411.4728v1).

- Theorem 1.2: for squarefree `n ≡ 5, 6, 7 (mod 8)`, if a parity sum `L_x(n)` of genus class
  numbers `g(d) = #2Cl(ℚ(√−d))`, `d | n`, is odd, then `ord_{s=1} L(E^{(n)}, s) = 1`. Hence
  rank 1 (Gross–Zagier–Kolyvagin) and finite Ш.
- Smith (arXiv:1603.08479, Thms 2.1, 2.2 and Table 2) rewrites `L_x(n) ≠ 0` as the
  nonvanishing of a bordered Monsky determinant `|M v; vᵀ 0|` (rows 5a/5b, 6, 7a/7b). Smith's
  Theorem 1.4: it implies `dim Sel₂ = 3`, and holds for half (`n ≡ 6`) or three quarters
  (`n ≡ 5, 7`) of the Selmer-minimal `n`. Smith's paper is an arXiv preprint (2016); I found no
  journal version. It is used here only as an equivalent F₂-linear-algebra form of TYZ's
  genus-class-number sums.
- My transcription of Table 2 (`tyz_smith.py`) passes three checks (VERIFIED):
  - Smith's `M₁` and `M₂` coranks reproduce `dim Sel₂ − 2` from `sel2cong.py` on 60 of 60
    `n ≡ 1, 2 (mod 8)`.
  - Every TYZ-certified `n` among 61 random `n < 10⁶` has `dim Sel₂ = 3`.
  - As `ω(n)` grows, the certified fraction of Selmer-minimal `n` tends to Smith's densities:
    0.69, 0.47 and 0.74 at `ω = 11`, against 0.75, 0.5 and 0.75. At small `ω` it is higher.

  The analytic rank (PARI) is 1 for all 530 TYZ-certified Selmer-minimal `n < 2000`. That check is weak, because by
  Kriz every Selmer-minimal `n` has analytic rank 1 anyway.
- So TYZ needs, for each curve that uses the converse, Selmer minimality plus one bordered
  determinant condition. §4.4 tests whether the descent can meet both. In the experiments it
  can: 60 of 60 inputs (30 random, 30 adversarial), with all certificates from TYZ.

### 4.4 The descent (VERIFIED computations; the lemma itself is SPECULATIVE)

**Method.** `sel2cong.py` computes `Sel₂(C_d)` exactly, independently of `scratch/rs-pole/`.

- Candidates: `⟨−1, 2, p | d⟩²`.
- Odd `p | d`: local image is the span of the three torsion images. It is 2-dimensional; the
  torsion images are independent because `±d` is a nonsquare at `p`.
- Real place: `(−,−)` for `d > 0`, `(−,+)` for `d < 0`.
- Place 2: images of explicit rational points of `C_{d₀}(ℚ₂)`, with `d₀ ≡ d` in `ℚ₂*/ℚ₂*²`,
  collected until dimension 3 (`= dim E(ℚ₂)/2E(ℚ₂)`) is reached. This is exact, since every
  sampled point is a genuine local point.
- Cross-checks:
  - against PARI's `ell2cover` on 30 curves, including Selmer rank 4 with `Ш[2] ≠ 0`
    (`d = 17`): 30 of 30 agree (`validate_sel2.py`);
  - against generators from `ellrank` on 30 random curves with `dim Sel₂ = 3`, `|d| < 4000`: in
    all 22 cases where `ellrank` returned a point, the images of the point and the torsion span
    exactly the computed Selmer group. In the other 8, `ellrank` certifies rank 1 without
    printing a point (`validate_points.py`).

**The 2-adic images** (VERIFIED). For `d ≡ 1, 7` the first coordinates are `{1, 7}`; for
`d ≡ 3, 5` they are `{1, 3, 5, 7}`; for even `d` they are all eight classes, bijectively. In
particular, for even `d` the second coordinate at 2 is determined by `β`.

**Necessary local conditions** for a class `(β, c)` on `C_{βn'}` or `C_{βn'θ}` (VERIFIED,
derived from the local images):

- At odd `p | β`: `n'` is `± □` mod `p`.
- At `q | n'`: `β` is `± □` mod `q`.
- At `p | θ`: automatic, since `β` is a square there.

So there is no local obstruction at 2 or `∞` for any `m`, as long as `n` may take any 2-adic
class.

**Experiments** (`descent_search.py` and the stress drivers). Inputs are fresh, from my own
generators: `B = N/D²`, `N = Πp^{e_p}·u`, with `e_p ∈ {4,…,7}` on `S₀` (so both parities at
`S₀`), `gcd(D, N) = 1` and `0 < B < 1/2`. Every input is asserted admissible.

| Test | Inputs | Result |
| --- | --- | --- |
| random (`u < 10⁷`, `D` up to `50√(2N)`) | 30 | **30 of 30** solved. 29 with `n = β` (no auxiliary prime; the multiplier is the free parameter); 1 with one auxiliary prime. |
| many primes in `β` (6–9 primes `< 300` in `u`; `ω(β)` up to 14) | 10 | 9 by the quick search (`k ≤ 2` primes `< 200`). The 10th by the two-phase search with `m = 5`, `n' = 971`. **10 of 10.** |
| fixed multiplier, `n' ∈ {1, θ}` forbidden, random auxiliary sets (`k ≤ 7`, primes `< 20000`) | 20 inputs × 6 multipliers | 109 of 120 pairs at once. Of the 11 failures, the 8 from the second batch were rerun with the two-phase search (primes up to `10⁶`): **8 of 8 solved** with 3–6 auxiliary primes. The 3 from the first batch were not retried. |
| fixed `m = 1`, `θ` built as a product of 4–9 small primes (`N = D² − θ₀Y²`) | 10 | **10 of 10** with `m = 1` fixed: 8 by plain random sampling (2–4 auxiliary primes, after 11–15,000 trials), #4 by the two-phase search (`n' = 119131·236773·311009`, re-verified), and #8 (`ω(θ) = 8`) after 60,586 trials (`n' = 27802123643865553`). Every solution was re-verified. |
| minimal `S₀` valuations (`e_p ∈ {4, 5}`), tiny cofactor | 10 | **10 of 10** (all `k = 0`) |
| extreme `B` (just below `1/2`, or `D ≈ 10¹⁷`) | 10 | **10 of 10** |
| **TYZ variant**: as above, but every curve that uses the converse must also pass TYZ's criterion | random 30; many-`β` 10; `S₀`-edge 10; extreme-`B` 10 | **30 of 30; 10 of 10; 10 of 10; 10 of 10.** Two many-`β` inputs needed the larger pool (`m = 5`, `n' = 87380822281`; `m = 105`, `n' = 93479`). |

**Observations.**

- **The multiplier carries most of the work.** With 64 multipliers, `n = β` succeeds for most
  inputs. Then only `C_{βθ}` needs the converse, because the class `β` on `C_β` is the torsion
  point `(β, 0)`.
- **For a fixed multiplier, auxiliary primes are needed, and when `θ` has many primes suitable
  ones are rare but exist.**
  - For the pair `B = 301705438760288079032880000/1164411428159110046935918403761`, `m = 6`
    (`β = 3·13·41·199·773`, `ω(θ) = 7`), the class `β` lay on `C_{nθ}` for only 5 of 3,000
    random `n'` (on both curves for 3), against 673 of 3,000 for `C_n`.
  - Its existence is decided by about `ω(θ)` Legendre conditions linking `θ`'s primes to the
    auxiliary primes. A proof must choose those symbols by Dirichlet, exactly as the manuscript
    does for `E_ℓ` (lines 1035–1061).
  - The structured searches (beam, two-phase, annealing) reported failures on the smooth-`θ`
    family. Plain random sampling of 2–10 primes up to `10⁶` (`brute_fixed_m.py`,
    `brute_smooth_all.py`) then solved all ten, with 2–4 auxiliary primes. The trials needed
    ranged from 11 to about 60,000; the hardest case is #8, where `ω(θ) = 8`. So the failures
    were artifacts of the searches. The two-phase search, for example, stopped sampling after six
    partial starts.
  - Likewise, with `ω(β) ≈ 10` most random products fail the necessary conditions at the primes
    of `β`. That is why some quick searches failed.
- **No invariant obstruction was found.** Three candidate invariants did not predict the rare
  failures (`out_obstruction_probe.txt`, `out_p0_probe.txt`):
  - products of quartic residue symbols `(β/p)₄` (`p | θ`) and `(θ/p)₄` (`p | β`);
  - `θ mod 16`;
  - the `n' = 1` case.

  Every pair retried with the larger search was solved. The 3 failures from the first
  fixed-multiplier batch were not retried, because their inputs were not recorded.

**The linear system** (VERIFIED, derived from the local images and used by `sel2cong.py`).

Let `d > 0` be odd and squarefree with primes `p_i`, and put `d_i = d/p_i`. Write a candidate
class as `a = (−1)^{α₀}2^{α₁}Π p_j^{u_j}`, `b = (−1)^{β₀}2^{β₁}Π p_j^{v_j}`. Put
`[x/p] = (1 − (x/p))/2 ∈ 𝔽₂` and `r_i(a) = α₀[−1/p_i] + α₁[2/p_i] + Σ_{j≠i} u_j[p_j/p_i]`,
and similarly `r_i(b)`. The condition at `p_i` depends on `(u_i, v_i)`:

| `(u_i, v_i)` | condition at `p_i` |
| --- | --- |
| `(0, 0)` | `r_i(a) = 0`, `r_i(b) = 0` |
| `(1, 0)` | `r_i(a) = [d_i/p_i]`, `r_i(b) = [2/p_i]` |
| `(1, 1)` | `r_i(a) = [−d_i/p_i]`, `r_i(b) = [−2d_i/p_i]` |
| `(0, 1)` | `r_i(a) = [−1/p_i]`, `r_i(b) = [−d_i/p_i]` |

The conditions at 2 and `∞` come from the table of 2-adic images above. The class `β` is the
specialization `u = 1_{supp β}`, `α₀ = [β < 0]`, `α₁ = [2 | β]`.

The descent lemma asks for auxiliary primes such that this system has exactly one solution class
beyond the torsion, with that specialization, for both `d = n` and `d = nθ`. For the TYZ
variant it must in addition satisfy Smith's bordered determinant for the residue class of `d`.

**What a proof must do (SPECULATIVE outline).** Write `n = βn'` with auxiliary primes of chosen
symbol type, as in the manuscript's slots. Arrange for both Monsky matrices (for `n` and `nθ`)
to have corank one with kernel containing the vector of `β`. The manuscript's argument (`ker K`,
the rank-one correction `K♯ = K + λaᵗ`, the block `(D₁ C₁; C₁ᵗ 0)`) is written for `E_ℓ` in
Kummer coordinates `(x + 3ℓ, x − ℓ)` with a 3-adic condition. It must be redone for the Monsky
matrix of `C_d` (Heath-Brown's appendix; Smith's `A`, `D_y`, `D_z`).

- The 2-adic part is simpler: the bad places are 2 and the primes of `d`, and there is no 3-adic
  condition.
- The simultaneous condition for `n` and `nθ` is as hard as before.
- Using all 64 multipliers instead of one fixed `m` helps only heuristically. A proof cannot rely
  on it unless it shows that some `m` always avoids every obstruction.

### 4.5 Everything else Route K changes (VERIFIED by grep; effort SPECULATIVE)

**Lean definitions.**

- `ZInQ.polePoly` (`Hypotheses/Pole.lean`, lines 28–29).
- `ZInQ.Syntax.poleT1` and `poleT2` (`Syntax/Templates/Core.lean`, lines 242 and 245), with
  their docstrings and `polePolyOf`.
- `ev_polePolyX` and `poleSystem_of_polePoly_eq_zero` re-run unchanged (`simp`/`rfl` on the new
  definitions).
- `poleTemplate_maj : Maj B 1 poleTemplate.poly` (`Size/Majorants/Templates.lean:61`) is proved
  by `size_maj`. The coefficients only get smaller (3 → 1), so the same statement holds.
- `poleTemplate_wf`, `poleTemplate_witnessScope`, `poleBuild_run`, `poleTemplate_params = 1` and
  `poleTemplate_witnesses = 11` are unchanged in statement.

**Lean valuation lemmas.**

- A new file with the `x + l` copy of upstream's `curve_rhs_nonzero_and_valuation` and
  `poleSystem_no_negative_odd_valuation`. Upstream `lean/` is frozen, so the copy goes in
  `ZInQKernel`.
- `abscissa_val_even` and `pole_obstruction` (`Parity.lean`) and `poleSoluble_no_negative_odd`
  (`PoleObstruction.lean`) re-pointed to the copy. The hypothesis `p ≠ 3` disappears, and the
  statement `p ∤ 2730` stays.

**What does not change in Lean.**

- The call sites `slope_complete` and `test_complete`, and everything in the size chain and the
  compiler.
- No constant depends on the factor 3.
- The degree of `Q_pole^C` is still 75: `T₂` contains the monomial `−A e²H²` of degree 37
  whether the factor is 1 or 3.

**Frozen target.** The variable count is kept exactly. The template still has 1 parameter and 11
witnesses, so `P_*` keeps exactly 292,890,231,905 variables, and the degree and coefficient
bounds still hold. Only coefficients of `P_*` inside the pole blocks change. The target statement
needs no edit.

**Outside Lean.**

- `construction/multiplication-certificate.js` (the `pole` definition, line 22),
  `construction/variable-shift-polynomial-library.js` and the saved `P_*` JSON.
- The manuscript:
  - Section 5: `Q_pole` at lines 979 and 986; Theorem 5.3 replaced by a citation of Kriz plus
    Lemma 5.4 (Poonen–Stoll); the descent at lines 1019–1121 rewritten for `C_ℓ`.
  - Lemma 5.5 (forward rank, A020/A082) is no longer needed in Section 5, because Kriz gives the
    rank directly.
  - In the TYZ variant, Section 5 instead cites TYZ Theorem 1.2 (with Smith's Theorem 2.2, or a
    direct proof of the needed F₂ identity) and Gross–Zagier–Kolyvagin (A020). Lemma 5.4
    (Poonen–Stoll) is then unnecessary: rank 1 with finite Ш and `dim Sel₂ = 3` already force
    `Ш[2] = 0`.
  - Sections 7–9 and Appendices E–G, and the 39 RC-only audit records, become unnecessary.
  - Lemma 1.2 and line 128 updated.
- The audit adds one record for Kriz (Theorems 1.1, 9.23, 10.13, 10.17(2), with the `f₀ ≤ 3`
  remark above).

## 5. Ranking and recommendation

| Rank | Route | Gain | Chance |
| --- | --- | --- | --- |
| 1 | **K-Kriz: Route K with a proved descent lemma** (auxiliary primes by Dirichlet) | PC follows from Kriz, Poonen–Stoll and an elementary lemma; RC (8,000 lines, 39 audit records) disappears | medium–high |
| 2 | **K-TYZ**: the same, with Tian–Yuan–Zhang's published criterion (in Smith's determinant form) on each curve that needs the converse | only published deep inputs remain: TYZ, plus Gross–Zagier–Kolyvagin, already A020; Poonen–Stoll is not needed | medium; the lemma needs one extra bordered-determinant condition per curve, which all 60 test inputs met |
| 3 | K-L: state in Lean the narrow hypothesis "a congruent number curve with `dim Sel₂ = 3` (resp. passing TYZ) has a point with each Selmer first coordinate" and prove the descent in Lean | the hypothesis becomes a direct corollary of a cited theorem | medium, given 1 or 2 |
| 4 | Keep `E_ℓ` and RC | no change | (status quo) |

**Recommendation.** Prove the descent lemma for congruent number curves with the multiplier
chosen by the 2-adic class of `β`. Use the manuscript's slot construction (lines 1035–1061),
transposed to the linear system of §4.4. Prove it first in the Kriz form, then check whether one
further auxiliary slot can also force Smith's bordered determinant (K-TYZ). Test each step
against `scratch/rv-route-k/sel2cong.py` and `tyz_smith.py`.

- **Success criterion.** A written proof that, for every admissible input and the chosen `m`,
  there are auxiliary primes making both `C_n` and `C_{nθ}` Selmer-minimal and containing the
  class `β`. Validate it by running the algorithm it yields on the smooth-`θ` family
  (`descent_search.py`, generator `smooththeta`). Each output must pass `sel2cong.py`.
- **Chance: medium–high**, for these reasons:
  - The deep input fits exactly, and soundness transfers.
  - Every input and every fixed `(B, m)` pair retried with the larger search admitted a
    solution, with at most six auxiliary primes.
  - No invariant obstruction appeared.
  - The analogous lemma for `E_ℓ` was already carried out in the manuscript, with an extra
    3-adic condition that `C_ℓ` does not have.

  The remaining risks:
  - Writing the simultaneous condition for `n` and `nθ` cleanly. When `θ` has many primes the
    suitable auxiliary symbol patterns are a small fraction, so the proof must choose them
    rather than count on them.
  - Kriz's theorem is unrefereed. The TYZ variant removes that risk at the cost of a stronger
    lemma.

## Scripts (in `scratch/rv-route-k/`)

| Script | Purpose |
| --- | --- |
| `sel2cong.py` | exact 2-Selmer groups of `C_d` |
| `validate_sel2.py` | comparison with PARI `ell2cover` and `ellrank` (30 curves) |
| `validate_points.py` | Selmer classes against actual generators |
| `reform_check.py` | parametrization, 40 explicit zeros of `Q_pole^C`, the `θ = 1` witness |
| `descent_search.py` | generators and searches: `random`, `manybeta`, `smooththeta`, `edgeS0`, `extremeB`; drivers `first`, `stress`, `stressrand` |
| `beam_search.py`, `twophase.py`, `anneal.py` | structured auxiliary-prime searches for a fixed multiplier (they under-perform) |
| `brute_fixed_m.py`, `brute_smooth_all.py` | plain random auxiliary-prime search for a fixed multiplier, with re-verification |
| `tyz_smith.py` | Smith's determinant form of TYZ, and its validation |
| `descent_tyz.py`, `brute_tyz.py` | the descent with TYZ certificates (`KRIZ=1` switches `brute_tyz.py` back to the Kriz criterion) |
| `smooth_theta_test.py` | the smooth-`θ` family with fixed `m = 1` and the two-phase search |
| `diagnose_fixed_m.py`, `diagnose_pair.py`, `presence_beam.py`, `obstruction_probe.py`, `p0_probe.py` | diagnosis of the fixed-multiplier failures |

Outputs are in `out_*.txt`.
