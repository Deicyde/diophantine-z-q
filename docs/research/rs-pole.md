# Pole completeness and the restricted converse

This note studies hypothesis PC (`ZInQ.PoleCompleteness`, manuscript Theorem 5.2, line 1001)
and the restricted converse RC on which the manuscript bases it (Theorem 5.3, line 1005; proof
in Sections 7–9, lines 1760–5745, and Appendices E–G, lines 6825–10935). Every claim carries one
of three marks:

- **VERIFIED**: checked against the manuscript, the Lean sources or the cited source text, or by
  an exact computation (scripts in `scratch/rs-pole/`).
- **STANDARD**: a published theorem, with a reference.
- **SPECULATIVE**: an idea or expectation that is not proved.

Notation. `E_ℓ : y² = x(x − ℓ)(x + 3ℓ)` are the manuscript's curves (the π/3-congruent number
curves of Fujiwara and Kan, quadratic twists of the conductor-24 curve `E_1`).
`C_ℓ : y² = x(x − ℓ)(x + ℓ) = x³ − ℓ²x` are the congruent number curves. For a nonzero
rational `r`, `sqf(r)` is its signed squarefree part. For a pole input `B` and a multiplier `m`
(a signed divisor of 2730), put `A = mB`, `H = A(A − B²) = mB²(m − B)`, `β = sqf(A)`,
`θ = sqf(H) = sqf(m(m − B))`.

## 1. The statement and every use

### 1.1 Statement

`Φ(B)` (`ZInQ.PoleSoluble B`) asserts that the eleven-witness polynomial `Q_pole`
(`ZInQ.polePoly`, manuscript lines 979–987) has a rational zero with input `B`. For `B ≠ 0` a
zero amounts to a signed divisor `m` of 2730, a rational `e` and a rational `z` with

- `(A, r₁) ∈ E_e(ℚ)`, and
- `(Az², z r₂) ∈ E_{eH}(ℚ)`, with `eHz ≠ 0`.

(VERIFIED, from the definition.) PC states: if `B` has square reduced denominator, `0 < B < 1/2`
and `v_p(B) ≥ 4` for `p ∈ S₀ = {2, 3, 5, 7, 13}`, then `Φ(B)`.

The soundness direction uses only the one-sided obstruction (Lemma 5.1, line 988): if `B ≠ 0`
and `Φ(B)`, then `v_p(B)` is not negative and odd for `p ∉ S₀`. In Lean this is
`ZInQ.Assembly.poleSoluble_no_negative_odd` (`Assembly/Local/PoleObstruction.lean`), proved from
upstream's `ZInQ.ValuationObstruction.poleSystem_no_negative_odd_valuation`
(`lean/ZInQ/PoleValuation.lean`). It is a theorem, not part of the hypothesis. (VERIFIED)

### 1.2 Uses in Lean

`grep PoleCompleteness ZInQKernel` gives exactly two places where the hypothesis is applied.
Every other occurrence only passes it along (`completeness_core`, `multiply_complete`,
`multiplication_exact`, `value_relation_iff_of`, `Pstar_spec`, `assembly`, the main theorems in
`Main.lean`). (VERIFIED)

| Lean declaration | Manuscript | Input fed to PC |
| --- | --- | --- |
| `ZInQ.Mult.slope_complete` (`Multiplication/Completeness/SlopeCompleteness.lean`, applied at the last line) | completeness of the slope certificate, lines 1704–1751 | `B = R/Θ²` with `R = ℓ₀² a² R₀`, `R₀ = ηF(t)/(t − 1)⁸`, `a = 1 − R₀q²`, `Θ = Tr Σ_g W_g⁻¹`, `W_g = Π_j (1 + R C_{gj}²)` |
| `ZInQ.Assembly.test_complete` (`Assembly/Local/TestCompleteness.lean`) | Lemma 11.2 (one suitable shift), lines 6202–6234 | `B = testR/poleTheta²` with `testR = R₀ a₀²`, `R₀ = η·2730⁶·F(n)`, `a₀ = 1 − R₀q²`, `Θ = Tr W⁻¹` |

In both cases the conclusion `Φ(B)` is placed directly into an existential predicate (`SlopePred`,
resp. `Test`) whose witnesses include the rational `q`. The proofs choose `q` by weak
approximation (`weak_approx_q`, resp. `poleInput_real`) and then verify PC's hypotheses
(`pole_input_valuations`, `pole_input_small`, resp. `poleInput_local`). (VERIFIED)

### 1.3 Uses in the manuscript

Completeness of multiplication (line 1751, "Theorem 5.2 supplies the required pole witnesses")
and Lemma 11.2 (line 6233). The sound directions (lines 1196 and 6167) use only Lemma 5.1.
Lemma 1.2 lists PC as one of the six inputs of the assembly (line 101). (VERIFIED)

## 2. The weakest form the proof needs

### 2.1 Structural slack in the input

**(a) The square class of the input is fixed; only a square factor moves.** In both uses
`B = R₀ · s²` with `s = ℓ₀a/Θ` (slope), resp. `s = a₀/Θ` (test). The class `R₀ ℚ*²` is fixed by the
slope `t` (it is the class of `ηF(t)`), resp. by the integer `n` (the class of `ηF(n)`). Only `s`
depends on the free witness `q`. Consequently `β = sqf(mR₀)` does not depend on `q`, while
`θ = sqf(m(m − R₀s²))` does. (VERIFIED from `slopeR`, `testR`)

**(b) One `q` per instance suffices.** PC asserts `Φ(B)` for every admissible `B`. The proofs
need it for one `B(q)` per instance, where `q` ranges over an open subset of
`ℝ × Π_{p∈S} ℚ_p` for an explicit finite `S`. A strictly weaker hypothesis that still suffices
for both uses:

> **PC⁻.** For every instance (slope data, resp. `n, κ`) and every nonempty open set of `q`
> satisfying the local conditions of `weak_approx_q`, resp. `poleInput_real`, some rational `q`
> in it has `Φ(B(q))`.

No known argument uses this freedom, and §4.3 explains why explicit-point arguments cannot use it
naively. It is recorded for completeness. (VERIFIED that it suffices; usefulness SPECULATIVE)

**(c) Numerical thresholds.** The call sites supply more than PC asks:

- `v₂(B) ≥ 4` and `v_p(B) ≥ 6` at `p = 3, 5, 7, 13` (test, `poleInput_local`);
- `v_p(B) ≥ 103C_p + 8` on `S_b` (multiplication, line 1745).

The descent (§3.1) uses these valuations only to make `1 − B/m` a local square at `S₀`, so that
`θ` is a local square there. That needs only `v₂(B/m) ≥ 3` and `v_p(B/m) ≥ 1` for odd
`p ∈ S₀`. The bound `0 < B < 1/2` is used only to make `m − B > 0` for the chosen positive
`m ≥ 1`, so `B < 1` would do. (VERIFIED by reading lines 1019–1040; the thresholds have slack
but nothing is gained by lowering them.)

### 2.2 An exact reformulation of `Φ`

Put `g_β(t) = β(βt² − 1)(βt² + 3)` for `t ∈ ℚ`, and `g_β(∞) = β`.

**Proposition 1.** For `B ≠ 0`, `B ≠ m`: `E_ℓ` has a rational point with abscissa in `βℚ*²` if
and only if `ℓ ∈ g_β(ℙ¹(ℚ))·ℚ*²`. Consequently `Φ(B)` holds if and only if, for some signed
divisor `m` of 2730, there are `t₁, t₂ ∈ ℙ¹(ℚ)` with

```
θ · g_β(t₁) · g_β(t₂) ∈ ℚ*².
```

*Proof.* Scaling `(x, y, ℓ) ↦ (λ²x, λ³y, λ²ℓ)` reduces the first claim to a point with `x = β`.
That condition, `(β − ℓ)(β + 3ℓ) ∈ βℚ²`, is a conic in `(ℓ, w)` with the rational point
`(β, 0)`. The lines through that point give `ℓ = β(βt² − 1)/(βt² + 3)`. For `Φ`: `A/β` and `H/θ`
are squares, so the curves needed are `E_e` with `e ≡ g_β(t₁)` and `E_{eH}` with
`eH ≡ eθ ≡ g_β(t₂)` modulo squares. Given `(t₁, t₂)`, the witnesses are explicit:
`e = ℓ(t₁)·A/β`, `z² = (eH/ℓ(t₂))·β/A`, `w = (eHz)⁻¹`, and `r₁, r₂` are rescaled ordinates.
(VERIFIED: derivation; `scratch/rs-pole/phi_search.py` builds the eleven witnesses from
`(m, t₁, t₂)` and checks `Q_pole = 0` exactly in `ℚ`.)

Four consequences:

1. **Only the abscissa class matters.** `Φ` needs a point whose `x` lies in `βℚ*²`, that is, `β`
   in the image of the Kummer map of the 2-isogeny with kernel `(0, 0)`. The manuscript asks for
   the full Kummer class `(β, 1)` in coordinates `(x + 3ℓ, x − ℓ)` (line 1041). That is
   stronger than needed. (VERIFIED)
2. **The trivial case `θ = 1`.** Take `t₁ = t₂`. Explicitly: if `m(m − B) = c²` with `c ≠ 0`,
   then `e = A`, `z = c`, `r₁ = r₂ = 0`, `w = (A³c³)⁻¹` is a zero of `Q_pole`. It uses the
   2-torsion points `(A, 0) ∈ E_A` and `(Ac², 0) ∈ E_{Ac²}`. (VERIFIED by computation,
   `toy_validate.py`.) More generally the 2-torsion handles exactly the cases where `θ` is a
   product of two torsion values, and since `θ > 0` this means `θ = 1`.
3. **A one-curve sufficient condition.** Take `t₁ = ∞`, that is `e = A`, so that the first point
   is the 2-torsion point `(A, 0) ∈ E_A`. Since `AH = A²(A − B²) ≡ B(m − B)` modulo squares,
   `Φ(B)` follows as soon as, for some signed divisor `m` of 2730,

   ```
   E_{B(m − B)} has a rational point with abscissa in mB·ℚ*².
   ```

   This is one curve per multiplier, with no auxiliary parameter. In the sample computations of
   §4.1 it already suffices for 24 of 30 inputs (congruent family) and for 30 of 30 (π/3
   family). With only sixteen positive multipliers it cannot be guaranteed in general, so the
   descent needs the auxiliary primes of `n` as a fallback. (VERIFIED: derivation; the toy
   certificate with `θ = 409`, `(t₁, t₂) = (∞, −1/15)`, is of this kind)
4. **The surface.** `w² = θ g_β(t₁) g_β(t₂)` is a double cover of `ℙ¹ × ℙ¹` branched along a
   curve of bidegree `(4, 4)`: a K3 surface of Kummer type. Its rational points correspond to
   squareclasses `d` such that two quadratic twists `y² = d g_β(t)` and `y² = dθ g_β(t)` of a
   genus-one curve both have points, which are 2-coverings of `E_d` and `E_{dθ}`. PC is
   therefore a Hasse-principle statement for a family of Kummer surfaces. The descent below
   proves it via BSD-type input. (VERIFIED: the algebra; the K3 identification is STANDARD)

The test of `phi_search.py` on six realistic admissible inputs (`B = 2⁴3⁶5⁶7⁶13⁶u/v²`,
`0 < B < 1/2`) found no solution with `t₁, t₂` of height ≤ 12. This is expected: `θ` has prime
factors of about 20 digits, and every prime of `θ` must divide `g_β(t₁)g_β(t₂)`. Small-height
search cannot witness PC in practice. (VERIFIED, computation)

### 2.3 What the descent actually requires

Section 5.1 (lines 1019–1121) proceeds in two steps.

1. It chooses `m > 0`, then a positive squarefree `n ≡ 11 (mod 12)` that contains `β` and further
   auxiliary primes. The choice is made by reciprocity, CRT and Dirichlet, so that `E_n` and
   `E_{nθ}` both have `dim Sel₂ = 3` with the extra class `(β, 1)`.
2. It applies RC to `n` and `nθ`, then the forward theorem (the lemma "Forward analytic rank zero and one", line 1086), to get rank one
   and finite Ш. Hence `Ш[2] = 0`, so the class comes from a point, and the points give the
   eleven witnesses.

What is actually used (VERIFIED, by tracing the argument):

- **Two curves per input, and an existential choice.** RC is a universal statement over all
  squarefree `ℓ ≡ 11 (mod 12)`. PC uses it only for `ℓ ∈ {n, nθ}`, where `n` is any member of an
  infinite family `N(β, θ)` that the descent may enlarge with further conditions. The needed
  statement is:

  > **RC∃.** For each admissible `(β, θ)` there is `n ∈ N(β, θ)` such that `E_n(ℚ)` and
  > `E_{nθ}(ℚ)` both have positive rank.

- **Rank ≥ 1 is enough.** If `dim Sel₂ = 3` and `E(ℚ)[2] ≅ (ℤ/2)²`, then rank ≥ 1 already
  forces `E(ℚ)/2E(ℚ) = Sel₂` and `Ш[2] = 0`. Equivalently, the needed input is finiteness of
  `Ш(E_ℓ)[2^∞]` for these two `ℓ`. By Cassels–Tate (the lemma "Dimension three gives corank one", line 1072) the only alternative
  is rank 0 with `Ш[2^∞] ⊇ ℚ₂/ℤ₂`.
- **Kolyvagin is not needed after RC.** Once `L′(E_ℓ, 1) ≠ 0` and the root number is `−1`,
  Gross–Zagier alone gives a non-torsion Heegner point, hence rank ≥ 1, and the previous point
  finishes. Kolyvagin's theorem (A020) supplies finiteness of Ш, which Selmer minimality makes
  unnecessary here. (VERIFIED, logic; GZ is STANDARD)
- **Modularity is elementary here.** Every `E_ℓ` is a quadratic twist of `E_1`, which has
  conductor 24 (VERIFIED, PARI `ellglobalred`). The modular curve `X₀(24)` has genus one, and
  conductor 24 has a single isogeny class (STANDARD, Cremona's tables). Twisting a newform by a
  quadratic character gives a newform. So BCDT (A066) can be replaced by a classical statement
  for this family. (STANDARD)
- **The class must contain `β`.** A point with abscissa class `β` forces every prime of `β` to
  divide `ℓ`, since at a prime of good reduction a point has abscissa of even valuation. So
  `supp β ⊆ supp n` and `ω(n) ≥ ω(β)`, which is unbounded. (VERIFIED) This rules out any input
  restricted to twists with boundedly many prime factors (Heegner–Birch–Monsky type results for
  prime twists, or nonvanishing results for twists with few prime factors).

## 3. The manuscript's proof and its trust leaves

### 3.1 Structure

- **PC from RC** (lines 1019–1121): local squareclass bookkeeping with the multipliers
  (2730 = 2·3·5·7·13 realizes every real, 2-adic and 3-adic signature); then an explicit Rédei-type
  matrix construction of `n` (the matrix `K`, rank-one correction, auxiliary prime slots); then
  the corank lemma (line 1072, Poonen–Stoll); then RC twice; then the forward lemma (line 1086);
  then rescaling to the eleven witnesses.
- **RC** (Sections 7–9 and Appendices E–G, roughly 8,000 lines). Its own dependency order is
  stated at line 1818. It is a 2-adic induction on genus points and twisted central values:
  a Kato Euler-system even coefficient bound, a varying-companion arithmetic estimate proved by
  two limits over Selmer complexes, a genus-point lower bound via the explicit Gross–Zagier
  formula, normalization of odd half-integral-weight coefficients via Waldspurger, a common
  binary family, and finally a fixed-field determinant argument. That argument excludes
  `L′(E/K, 1) = 0` by contradiction (lines 5737–5745), so a rational point appears only
  afterwards, through Gross–Zagier and Kolyvagin. (VERIFIED by reading the section skeleton.) It
  is a new 2-converse for a non-CM family with full 2-torsion. It is not a published theorem.
  Kriz–Li (arXiv:1606.03172, Remark 1.6) note that the 2-converse was not known in 2018, and
  their own 2-adic method assumes `E(ℚ)[2] = 0`. (VERIFIED from the source text)

### 3.2 External theorems imported (from `docs/theorem-application-audit/applications.json`, anchors in lines 980–1125, 1760–5745, 6825–10935)

| Record | Theorem | Where used |
| --- | --- | --- |
| A019 | Poonen–Stoll, Cassels–Tate pairing alternating on the quotient by the divisible part | corank lemma, line 1072 |
| A020 | Kolyvagin MPI/90-69 Thm 1; Gross–Zagier; Kato Cor. 14.3; BCDT | forward lemma, line 1086 |
| A022 | Dokchitser–Dokchitser, Selmer parity (Thm 1.8) | root number −1 under corank one |
| A023, A049–A051 | Kato's Euler system: divisibility, lattice, reciprocity, norm relations | even coefficient bound |
| A024 | Hoffstein–Luo, nonvanishing with bounded prime support | companions |
| A025 | Bump–Friedberg–Hoffstein, odd nonvanishing | genus partner |
| A026 | Desjardins, local root numbers of twists | sign bookkeeping |
| A027 | Cai–Shu–Tian, explicit Gross–Zagier (Thm 1.1) | genus lower bound |
| A028, A052 | Cornut–Jetchev; Voight; Jetchev–Kane | oriented supersingular reduction, ternary theta |
| A029–A031 | Waldspurger; Ramsey | half-integral weight coefficients |
| A032 | Carayol; Casselman | local `U_p` |
| A033 | Serre, open image (non-CM) | Galois images |
| A034, A035, A070 | Cai–Chen–Liu Heegner points; Howard; Elkik | Heegner classes and norm relations |
| A036–A045, A075, A080, A081 | Lang; Milne ADT; Nekovář's Selmer complexes | finite models, duality, Euler characteristics |
| A053, A054 | Weil representation, theta modularity | theta series |
| A057, A067, A068 | Dirichlet; Chebotarev; class field theory | prime choices (also used in §3.1) |
| A066 | BCDT modularity; Milne MF | modular parametrization |
| A069, A071, A073, A074, A076, A078 | Edixhoven; formal groups; S-units; Schreier; compactness; tame covers | auxiliary |
| A082 | forward analytic rank zero (Kolyvagin, Kato) | inside RC |

The leaves that matter most are the novel argument itself and the many published theorems it
assembles. A reader who trusts every cited theorem still has to trust about 8,000 lines of new,
unrefereed reasoning.

## 4. Candidate cheaper routes

### 4.1 Route K: rebuild the pole predicate on congruent number curves (main proposal)

**Idea.** Replace `E_ℓ` by `C_ℓ : y² = x(x − ℓ)(x + ℓ)` in `Q_pole`: `T₁ = A(A − e)(A + e)`,
`T₂ = A(Az² − eH)(Az² + eH)`. Then replace RC by a published 2-converse for congruent number
curves.

**The external input.** Kriz, *Supersingular main conjectures, Sylvester's conjecture and
Goldfeld's conjecture*, arXiv:2002.04767v5 (2022), Theorem 10.17(2), deduced from
Theorems 9.23 and 10.13 with `p = 2`, `K = ℚ(i)`: for `E_d : y² = x³ − d²x`,

```
corank_{ℤ₂} Sel_{2^∞}(E_d/ℚ) ≤ 1  ⟹  ord_{s=1} L(E_d, s) = rank E_d(ℚ) = corank, and Ш(E_d/ℚ) is finite,
```

for every squarefree `d`. Theorem 10.13 states this for every `E/ℚ` with CM by `O_K` and `p`
ramified in `K`. (VERIFIED against the arXiv v5 text, pp. 197–199. Publication status in a
journal is to be checked. STANDARD in the sense of an expert's complete preprint, used as such
in the literature.) This is exactly RC for the congruent family, for all `d`, with no
congruence condition. Tian–Yuan–Zhang (Asian J. Math. 21 (2017) 721–773) prove a published
special case: analytic rank one for `n ≡ 5, 6, 7 (mod 8)` under 2-class-group (Rédei)
conditions. That could serve if those conditions can be met for both `n` and `nθ`. (STANDARD;
the exact hypotheses were not checked here because the text could not be retrieved)

**What it replaces.** Theorem 5.3 and its proof (Sections 7–9, Appendices E–G), together with
audit records A022–A054 and A069–A082 as far as they serve RC. PC's proof would become:

1. local bookkeeping;
2. a Rédei-matrix construction of `n` for `C_n` and `C_{nθ}`;
3. the corank lemma (line 1072, Poonen–Stoll);
4. Kriz's theorem;
5. rescaling.

**Why it should work.**

- *Soundness is unchanged.* The proof of Lemma 5.1 uses only that for a `p`-unit parameter `ℓ`
  and odd `p`, the cubic has valuation `v(x)` when `v(x) > 0` and `3v(x)` when `v(x) < 0`.
  This holds for `x(x − ℓ)(x + ℓ)` exactly as for `x(x − ℓ)(x + 3ℓ)`. So the obstruction holds
  with the same `S₀` (2 must stay in `S₀`, as it does). (VERIFIED by reading lines 993–999)
- *The local conditions simplify.* `C_ℓ` has bad reduction only at 2 and the primes of `ℓ`, so the
  3-adic bookkeeping disappears. For every `m` dividing 2730 with `m > 0`, `θ` is a square at 2
  and at every prime of `S₀` (because `v₂(B/m) ≥ 3` and `v_p(B/m) ≥ 1`). `β` is a square at
  every prime of `θ`, and `θ` at every prime of `β` (the manuscript's argument, lines 1027–1033,
  does not depend on the curve). The positive divisors of 2730 represent all eight classes of
  `ℚ₂*/ℚ₂*²` (1, 3, 5, 7, 2, 6, 10, 14). (VERIFIED)
- *The Selmer engineering works on samples.* `scratch/rs-pole/selmer_descent.py` computes 2-Selmer
  groups exactly by complete 2-descent. Global candidates are supported on the bad primes; local
  images are the span of the 2-torsion at odd bad primes and are obtained by `p`-adic sampling at
  2 (and 3) and at the real place. Linear algebra is over `𝔽₂`. Against PARI's `ellrank` on 19
  curves `C_N` and 19 curves `E_N`, `N ≤ 119`, it gives `dim Sel₂ = 2 + rank` in every case.
  On realistic admissible inputs `B` it searches over `m > 0` dividing 2730 and over
  `n = β·n′`, with `n′` a product of at most four primes in `[5, 281]` (prefiltered by the
  necessary Legendre conditions). It asks that `C_n` and `C_{nθ}` both have `dim Sel₂ = 3` and
  contain a class with first coordinate `β`. The inputs were 30 random
  `B = 2⁴3⁶5⁶7⁶13⁶u/v²` with `u < 1000`, `gcd(v, 2730) = 1` and `0 < B < 1/2`. (Then
  `v₂(B) ≥ 4`, `v_p(B) ≥ 6` on `S₀`, and `θ` has prime factors of up to 22 digits; the script
  asserts admissibility, `θ ≡ 1 (mod 8)` and `gcd(θ, 2730) = 1`.)
  **Result: a suitable `(m, n)` exists for 30 of 30 inputs**, each found in at most 2 s. In 24
  cases `n = β` works. Then the class `β` on `C_β` is the 2-torsion point `(β, 0)`, and only the
  single curve `C_{βθ}` needs the converse. The other 6 need one auxiliary prime. For two
  solutions the curve `C_n` is small enough for PARI to find a generator (`n = 193285` and
  `n = 1430`, from a preliminary run). Its abscissa class is `β` times a torsion class, as the
  descent predicts (`check_points.py`). An earlier sampler that did not enforce
  `gcd(v, 2730) = 1` produced inadmissible inputs (with `θ ≢ 1 (mod 8)`). Those account for the
  only two failures seen, which is consistent with the role of the `S₀` hypothesis.
  (VERIFIED, computation, on the samples stated)
- *The same test for the manuscript's family.* For `E_ℓ` the same search also succeeds for 30 of
  30 admissible inputs, all with `n = β` (torsion on `E_β`, Selmer-minimal `E_{βθ}`). But only 4
  of the 30 solutions have `n` and `nθ ≡ 11 (mod 12)`, which is the domain of RC. The weakened
  reduction of §2.3 would need RC beyond its stated congruence class. Kriz's theorem has no such
  restriction. (VERIFIED, computation)

**Main obstacles.**

1. The general existence of such `n` for every admissible `(β, θ)` must be proved: the analogue
   of the manuscript's matrix argument (lines 1035–1061) for the Monsky matrix of congruent
   number curves. It is elementary (Legendre symbols, reciprocity, CRT, Dirichlet), and the
   samples suggest a solution is easy to find. A proof is not written. (SPECULATIVE)
2. Trust moves from an unrefereed 8,000-line argument to Kriz's 214-page preprint. That is a large
   improvement in confidence and auditability, but the input is still deep. In Lean it remains
   a hypothesis.
3. The construction changes. Changing `Q_pole` changes the saved polynomial `P_*`
   (`construction/*.json`, external cross-checks only). In Lean it touches the following.
   (VERIFIED by `grep`; effort SPECULATIVE)
   - `polePoly` (`Hypotheses/Pole.lean`), and `poleT1`, `poleT2` (`Syntax/Templates/Core.lean`).
     The template is symbolic, with the majorant `poleTemplate_maj`.
   - A congruent-curve copy of upstream's obstruction lemma (`lean/ZInQ/PoleValuation.lean`,
     330 lines, which cannot be edited because `lean/` is the frozen upstream snapshot).
   - The parity lemmas that consume it (`Multiplication/Certificate/Parity.lean`,
     `Assembly/Local/PoleObstruction.lean`).

   The frozen target does not change, and the degree (75) and coefficient bounds of `Q_pole` do
   not grow.

**First test and success criterion.** Write the descent lemma for `C_ℓ`:

> For all coprime positive squarefree `β > 1`, `θ ≡ 1 (mod 8)`, each a local square at the
> primes of the other and `θ` prime to 2730, there is squarefree `n` with `β | n` such that
> `C_n` and `C_{nθ}` have `dim Sel₂ = 3` and contain a class `(β, ·)`.

It already holds on 30 random admissible inputs (§4.1, `selmer_descent.py`). Success means a complete
proof of the lemma, plus confirmation that Kriz's Theorem 10.13 has no further hypothesis (for
example on the conductor exponent at 2; the proof treats small `f₀` by LMFDB lookup). This makes
PC a corollary of Kriz's theorem.

### 4.2 Route P: keep `E_ℓ`, cite a published 2-converse

**Idea.** Replace RC's proof by a published `p = 2` converse for non-CM curves with full rational
2-torsion.

**Obstacle.**

- None is known to this note. Kriz's theorem needs CM with `p` ramified in the CM field.
- Skinner, W. Zhang and Sweeting need `p ≥ 3` or `p ≥ 5`. Using odd `p` would require
  controlling `Sel_p(E_n)` in the twist family. That group is not determined by local data the
  way `Sel₂` is: it behaves like a class group (Cohen–Lenstra), and no prime-by-prime construction
  controls it. (STANDARD for the cited results; the difficulty is SPECULATIVE)
- Kriz–Li's 2-adic Heegner congruences need `E(ℚ)[2] = 0`.

**First test.** A literature search on π/3-congruent numbers and on twists of 24a1 (genus points
à la Tian–Yuan–Zhang). Success: a published theorem "Rédei-minimal `Sel₂` ⟹ rank one" for twists
of 24a1. Chance: low.

### 4.3 Route E: explicit points, a parametrized family or a section

**Idea.** Choose `q` (or modify the construction) so that `B` lands where a point is explicit,
for example `θ = 1`, where 2-torsion gives the witnesses (§2.2).

**Obstacle (VERIFIED, as a lemma).** Let `U` be a `ℚ`-variety and `U → 𝔸¹²` a family of zeros of
`Q_pole` with `B ≠ 0`. The proof of Lemma 5.1 is purely `p`-adic. Hence for every `p ∉ S₀` and
every `y ∈ U(ℚ_p)`, `v_p(B(y))` is not negative and odd. For the slope inputs, at an odd contact
prime `p ∉ S_b` with `v_p(R₀) = k` odd and `v_p(q) = −N`:

- `v_p(R) = 3k − 4N`;
- each group has a nonzero first test (`w(H) ≠ 0` by the guard `H ≠ O`), so
  `v(W_g) ≤ 3k − 4N + O(1)` at every place above `p`, and `v_p(Θ) ≥ 4N − O(1)`;
- so `v_p(B) = v_p(R) − 2v_p(Θ) ≤ 3k − 12N + O(1)`, which is negative and odd.

So `B(q)` is bad on a `p`-adic neighborhood of `q = ∞`. In particular no family in which `q` is a
nonconstant polynomial in the parameters can exist, and any family must keep `q` `p`-adically
bounded at every contact prime of `t`, a set that depends on the factorization of `F(t)`. Making
`θ = 1` requires `m(m − R₀s(q)²) ∈ ℚ²`, a hyperelliptic curve of large genus in `q`. Making `s`
free while keeping soundness would require dividing `B` by the square of a factor constrained to
be `p`-integral at all primes. That is the definability problem itself.

**Assessment.** No cheap explicit route. Chance: very low.

### 4.4 Route N: nonvanishing instead of a converse

**Idea.** Use RC∃: find one `n` with `L′(E_n, 1) L′(E_{nθ}, 1) ≠ 0` via nonvanishing theorems
(Bump–Friedberg–Hoffstein, Murty–Murty, Iwaniec), then apply Gross–Zagier.

**Obstacle.** Selmer minimality (needed to place the class `β` in the image) depends on mutual
Legendre symbols of all primes of `n`, not on finitely many local conditions. On top of that, the
requirement is simultaneous nonvanishing for two forms twisted by the same `n`. No published
theorem covers this. Chance: low.

### 4.5 Route L: a narrower Lean hypothesis

**Idea.** Under Route K, state in Lean the hypothesis in the form actually consumed:

> For squarefree `n` and `d | n`, if the explicit local conditions hold (Legendre symbols at the
> primes of `2n`) and the explicit Monsky matrix over `𝔽₂` has corank one, then `C_n` has a
> rational point with `x ∈ dℚ*²`.

Then prove the descent (§4.1, obstacle 1) in Lean from Mathlib's Dirichlet theorem and quadratic
reciprocity.

- The Cassels–Tate step is absorbed into the hypothesis, so it need not be formalized.
- The hypothesis becomes a concrete Diophantine consequence of a cited theorem (Kriz plus
  Poonen–Stoll), instead of the current statement, which hides the whole descent.

**Obstacle.** Formalizing the Rédei/Monsky linear algebra and the prime choices is a substantial
elementary project.

**First test.** State the hypothesis and the descent lemma in Lean, the latter with `sorry`, and
check that `test_complete` and `slope_complete` close from them. Chance: medium-high once
Route K's lemma is written on paper.

### 4.6 Minor savings that hold for the existing route

- Kolyvagin (A020) is not needed after RC; Gross–Zagier suffices (§2.3). (VERIFIED, logic)
- BCDT (A066) can be replaced by modularity of `X₀(24)` plus twisting (§2.3). (STANDARD)
- The full Kummer class `(β, 1)` can be weakened to the abscissa class `β` (§2.2). This
  enlarges the admissible `n`. (VERIFIED)

None of these touches the main cost, which is RC.

## 5. Ranking and recommendation

| Rank | Route | Gain | Chance |
| --- | --- | --- | --- |
| 1 | K: congruent number curves + Kriz | removes the 8,000-line RC; PC follows from one cited theorem plus an elementary descent | medium-high |
| 2 | L: narrower Lean hypothesis (after K) | the hypothesis becomes a concrete arithmetic statement; the descent becomes Lean | medium-high, given K |
| 3 | K with Tian–Yuan–Zhang instead of Kriz | published journal source | medium (hypotheses unchecked) |
| 4 | P: published 2-converse for `E_ℓ` | keeps the construction | low |
| 5 | N: nonvanishing route | none beyond K | low |
| 6 | E: explicit points | would remove PC | very low (structural obstruction, §4.3) |

**Recommendation.** Pursue Route K. The next step is to write and prove the descent lemma for
congruent number curves (the statement in §4.1), test it with `selmer_descent.py` on 30 random
admissible inputs, and check Kriz's Theorem 10.13 hypotheses line by line.

- *Success criterion:* a complete written proof that every admissible `B` (square denominator,
  `0 < B < 1/2`, `v_p(B) ≥ 4` on `S₀`) admits `m` and `n` with `C_n`, `C_{nθ}` Selmer-minimal and
  containing the class `β`. Kriz's theorem then gives `Φ_C(B)` for the modified polynomial.
- *Chance: medium-high.* The input theorem exists and fits exactly. The local conditions for
  `C_ℓ` are simpler than for `E_ℓ`. The sample computations find suitable `n` with one to three
  small auxiliary primes. The risk is in the uniform combinatorial lemma: the 2-adic class
  bookkeeping and the simultaneous Rédei conditions for `n` and `nθ`. Those are elementary but
  fiddly; the manuscript needed a careful matrix argument for the analogous step. The second risk
  is that Kriz's theorem is, as far as this note could check, a preprint.

What Route K does not do: it does not remove PC from Lean. The deep input (a 2-converse) stays a
hypothesis. What changes is that the hypothesis becomes a published-quality theorem by an expert
instead of a new 8,000-line argument, and the remaining reduction is elementary enough to
formalize.
