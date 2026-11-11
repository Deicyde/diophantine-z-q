# rv-lit: adversarial review of the two literature reductions

Status: review note (task rv-lit, 2026-11-11, base `d7e15509`). Subject: `scratch/wk-cr3/Literature.lean`
with `docs/research/wk-cr3.md`, and `scratch/wk-h/BackToU.lean` with `docs/research/wk-h.md`. The note
also covers their adoption on `origin/wip/lit-adopt` (`9367dfa6`). The step log is
`scratch/rv-lit/log.md` and the scripts are in `scratch/rv-lit/`. No file under `ZInQKernel/`,
`blueprint/` or another note was edited.

Marks: **VERIFIED** (checked here, by Lean, by exact or numerical computation, or by reading a
source in the repository), **STANDARD** (published theorem; locators not read here),
**SPECULATIVE** (assessment).

## 0. Verdict

**Adopt the variants as drafted, with the two listed changes.** Those are `FunctionalEquation5`
restricted to `0 < Re s < 2`, and `GrossZagierKolyvagin` renamed `GrossZagier` with the twist
supplier corrected. lit-adopt made exactly these changes (§6). No further Lean repair is needed.
Every Prop the variants assume is true in Lean's semantics, given its cited theorem, and none is
vacuous or trivially true. Each Prop follows from its cited theorem and is never stronger.
`JHeightBound` is exactly the output of h-trust steps A1-F3.

Three repairs are needed in the notes. None blocks adoption (§7):

- **N1** (wk-cr3 §3): the faithfulness table calls the drafted `FunctionalEquation5` "true as
  stated". The draft is false (§1.2). The table also still cites Murty–Murty.
- **N2** (wk-cr3 §0, §1.3): "only TYZ among refereed theorems" depends on the publication status
  of Kriz's 2-converse, and that status is unknown.
- **N3** (wk-h §1): A9, C3 and C9 are classed W, but each contains a passage that is new in N5.
  By the note's own rule they belong to G (or a mixed class).

Attempts to refute that failed: junk values, quantifier scope, the Mathlib L-series at all
reduction types, conductor and root number, TYZ row 5b against analytic rank, the constant of
`JHeightBound`, and `twelve_mul_ratHeight_le`.

## 1. Truth and non-vacuity in Lean's semantics

### 1.1 The common definitions (VERIFIED by reading and Lean)

- `IsLContinuation E F` says that `F` is entire and that `F = E.LSeries` on `Re s > 3/2`. Mathlib's
  `LSeries f s` is a `tsum`, and its value is 0 when the sum is not summable. On `Re s > 3/2` the
  series converges absolutely, because Hasse gives `|a_n| ≤ d(n)√n` (STANDARD). So the junk value
  never constrains `F`. A half-plane `Re s > 1` would be wrong: there the `tsum` can be the junk 0,
  and no entire `F` could match it.
- `F` is unique (`IsLContinuation.eq`, Lean). So `∀ F` in `GrossZagier`, `FunctionalEquation5`,
  `RootNumberVanishing` and `TYZThm35ReadingA`, and `∃ F` in `TYZRow5b` and `HeckeContinuation`,
  differ only in whether `F` exists. It exists for every `E/ℚ`: by Breuil–Conrad–Diamond–Taylor,
  and for `C_d` by Deuring/Hecke (STANDARD). So the `∀ F` Props are not vacuous.
- `analyticOrderAt` takes the junk value 0 at a point where the function is not analytic. Lean
  confirms this (`scratch/rv-lit/Probe.lean`). It is never reached, because `F` is entire, so
  `analyticOrderAt F 1` is the true order. That order is not `⊤`, because `F ≢ 0`.
- The curve: `shortCurve (-(d : ℚ) ^ 2)` has `a₄ = -(d²)`. Lean proves this by `rfl` (Probe).
  So it is `C_d : y² = x³ − d²x`, isomorphic over `ℚ` to TYZ's `E_n : ny² = x³ − x`, with the same
  L-function.
- `GrossZagier` assumes `E.IsElliptic` (`Δ ≠ 0`). Mathlib's `LSeries` of a singular curve is not
  the L-function of anything standard, and the Prop never sees it.

### 1.2 The Props

| Prop | True? | Non-vacuous / non-trivial? |
| --- | --- | --- |
| `GrossZagier` | yes: Gross–Zagier with the auxiliary twist and BCDT (STANDARD), given §2 | `F` exists for every `E`; the conclusion is a real point of infinite order |
| `FunctionalEquation5` **as drafted** | **false** (VERIFIED). `Complex.Gamma 0 = 0` (Lean, Probe). At `s = 0` it gives `Λ(2) = −Λ(0) = 0`, but `L(C_d, 2) ≠ 0` (0.911, 1.024, 0.904 for `d = 5, 13, 21`; `fe_check.py`). It also fails at every `s` where `s` or `2 − s` is in `{0, −1, −2, …}` | — |
| `FunctionalEquation5` on `0 < Re s < 2` | yes. On the strip `Γ(s)` and `Γ(2 − s)` are the true values, and `N^{s/2}` and `(2π)^{−s}` are `cpow` with positive real base, so they agree with `exp(s/2 · log N)`. This is the textbook functional equation (STANDARD) with `N = 32d²` and `w = −1` (§3.2; numerically VERIFIED: `|Λ(2−s) + Λ(s)| < 2·10⁻¹⁷` at three points for `d = 5, 13, 21`) | yes; used at `s = 1` only |
| `RootNumberVanishing` | yes (Lean-derived from the previous row) | — |
| `TYZRow5b` | yes, given Proposition N and Hecke (§3.3). Sample check: 0 violations in 30 cases (§3.3) | asserts that `F` exists, so it is not vacuous; `T5bCl d = 1` holds for infinitely many `d` (26 of the 28 small `d` in §3.3) |
| `TYZThm35ReadingA` | yes, given Proposition N (first sentence) | the hypothesis `ord ≥ 2` occurs (`d = 26565, 33117`, rank 3) |
| `HeckeContinuation` | yes (STANDARD) | — |
| `JHeightBound Mult.S_mul` | yes, given h-trust A1-F3 (§4) | not trivial: it implies `SixContactMin` in Lean |

## 2. Mathlib's L-function against the standard `L(E, s)`

**By reading (VERIFIED; log Step 1).** The following match Silverman for every residue
characteristic:

- `localPolynomial` uses the minimal model over the completion (`IsMinimal` asks for the largest
  multiplicative valuation of `Δ` among integral models). Reduction is good if `v(Δ) = 0`,
  multiplicative if `v(Δ) > 0` and `v(c₄) = 0`, and additive otherwise (Silverman VII.5.1).
- `a = q + 1 − Nat.card (reduction).toAffine.Point`, where `Point` is `zero | some`, so the count
  includes the point at infinity. The factors are `1 − aT + qT²` for good reduction, `1 ∓ T` for
  split or nonsplit multiplicative reduction, and `1` for additive reduction.
- The split criterion is that `c₄T² + a₁c₄T − (54b₆ − 3b₂b₄ + a₂c₄)` splits. This is right in
  characteristics 2 and 3 too. The tangent slopes at the node solve `T² + a₁T − (3x₀ + a₂)`, and
  `c₄x₀ = 18b₆ − b₂b₄` holds identically over `ℤ` for a node translated from `(0,0)`. The node is
  rational because it is the unique singular point and `𝔽_p` is perfect.
- `q = Nat.card` of the residue field of `ℤ_p`, which is `p`. The `Nat.card` junk 0 needs an
  infinite residue field and never occurs.
- `invOfUnit` inverts a polynomial with constant coefficient 1. `ofPowerSeries p` puts the
  coefficient of `T^k` at `p^k`.
- `eulerProduct` is a `tprod` for the pointwise-discrete topology. It is multipliable because each
  coefficient stabilizes (`tendsTo_eulerProduct_ofPowerSeries`, Northcott). So it is the formal
  Euler product.

**By computation (VERIFIED, `an_check.py`).** The recipe was transcribed with PARI's global
minimal model and Mathlib's split polynomial, and compared with `ellan` up to `n = 300`. There
were 0 mismatches on 29 curves:

- `C_d` for `d = 5, 13, 21, 29, 37, 53, 1, 6, 7, 15, 34` (additive at 2 and at `p | d`);
- split multiplicative reduction at 2 (26b1, 34a1, `[1,1,1,1,1]`) and nonsplit at 2 (14a1, 26a1,
  30a1);
- split multiplicative reduction at 3 (21a1, 30a1) and nonsplit at 3 (15a1, 24a1, 33a1);
- non-minimal models.

The Lean side is noncomputable (classical choice of the minimal model), so it cannot be evaluated.
The comparison is against the definitions as read.

## 3. Faithfulness

### 3.1 `GrossZagier` (STANDARD)

Suppose `E/ℚ` is modular (BCDT 2001; for CM curves, Shimura) and `ord_{s=1} L(E, s) = 1`, so
`w(E) = −1`.

1. Choose an imaginary quadratic `K` in which every `p | N` splits (the Heegner hypothesis), with
   `L(E^K, 1) ≠ 0`. Bump–Friedberg–Hoffstein 1990 (via Waldspurger) or Friedberg–Hoffstein 1995
   give such `K`: they produce twists with prescribed local behaviour and nonzero central value.
   Murty–Murty 1991 (derivatives) gives the rank-0 input instead, so it is the wrong source. The
   correction is applied on lit-adopt.
2. Then `L'(E/K, 1) = L'(E, 1)L(E^K, 1) ≠ 0`. Gross–Zagier 1986 gives a Heegner point `y_K` of
   infinite order.
3. Since `w(E) = −1`, the trace `y_K` lies in `E(ℚ)` up to torsion.

The Prop states only "a point of infinite order". That is weaker than Gross–Zagier–Kolyvagin's
`rank = 1`. Its truth for every Weierstrass model uses the model-independence of Mathlib's L-series,
which holds because it is computed prime by prime from a minimal model. Non-minimal models were
checked in §2.

### 3.2 `FunctionalEquation5` (VERIFIED numerically; STANDARD)

For the first 30 squarefree `d ≡ 5 (mod 8)` (5 to 285), PARI gives conductor `32d²` and
`ellrootno = −1` (`fe_check.py`). The normalization `Λ(s) = N^{s/2}(2π)^{−s}Γ(s)L(s)`,
`Λ(2 − s) = wΛ(s)`, is the standard one, and PARI's `lfun` satisfies it to `10⁻¹⁷`. The citations
are Deuring/Hecke for the functional equation and Birch–Stephens 1966 for the sign. Restricted to
the strip, the Prop follows from the theorem.

### 3.3 `TYZRow5b` against nt-tyz (VERIFIED by reading; sample-VERIFIED)

The definitions match nt-tyz:

- `gCl n = Nat.card` of the image of squaring on `ClassGroup (𝓞 ℚ(√−n))`. That is `#2Cl`, TYZ's
  `g` (nt-tyz Notation).
- `T5bCl` sums `Π_B gCl(d_B)` over set partitions with one block `≡ 7`, one block `≡ 3` and the
  rest `≡ 1 (mod 8)`. That is nt-tyz's `T_5b = Σ g(d₀)g(d₁)𝓛₁(n/d₀d₁)`, where `𝓛₁` runs over
  partitions into class-1 blocks.
- `T5aCl` (new in the draft) uses one block `≡ 5` and the rest `≡ 1`, including the one-block
  partition `{n}`. That is reading A's `T_5a`.

**Is `TYZRow5b` exactly what Proposition N proves?** Proposition N says that if `T_5b(n)` is odd,
then `𝓛(n) ≠ 0` and `ord = 1`. By I7, `𝓛(n) = 0` exactly when `ord > 1`. So "`T5bCl d = 1` ⟹
`ord ≤ 1`" is the contrapositive of Proposition N's `T_5b` half. `TYZRow5b` is weaker than
Proposition N in two ways: it gives `≤ 1` rather than `= 1`, and it is stated through Mathlib's
L-series. It needs one input that Proposition N does not state: the existence of the continuation
(Hecke). The `∃ F` makes this explicit, and the documented route takes it as the separate Prop
`HeckeContinuation`.

`TYZThm35ReadingA` is Proposition N's first sentence, with "`𝓛(n) = 0`" read as `ord ≥ 2`.

**Independent sample (`tyz_sample.py`).** Fresh code for set partitions, `g = h/#Cl[2]` from
`quadclassunit`, and `ellanalyticrank` were run on 30 values of `d`: 26565 and 33117 (rank 3), and
the first 28 squarefree `d ≡ 5 (mod 8)` with at least two primes `≡ 3, 7 (mod 8)`. `T5b` is odd in
26 of them, and all 26 have analytic rank 1. Both rank-3 cases have `T5a = T5b = 0`. There are 0
violations of `TYZRow5b` or `TYZThm35ReadingA`.

## 4. The H side

**`J` is the value F2 bounds (VERIFIED by reading N5).**

- `F(u) = u(u+15)(u+20)(u+24)(u+30)(u+60)` and `G(u) = 7u² + 300u + 3600` (N5 L381-383). These
  are `Fh` and `Gh`.
- N5 L510 pulls back the `j`-line by `J(u) = −57600F²/G⁶`, and that is `Jmap`.
- At L949-950, N5 writes `j = a/b` and says that `−57600bF(X)² − aG(X)⁶` has `u` as a root. So F1
  and F2 concern `j = J(u)`, the fibre over `u`. `J(u)` is finite because `G` has no rational root,
  and nonzero because `u ∉ 𝒞`.
- F1's constant checks: `16·144⁵·2⁻¹⁸ = 2⁶3¹⁰ = 3779136`.

**The constant (VERIFIED).**

- F2 (L928-932): `h(j) ≤ 40h([z_m]) + 22`. The `ℓ¹` norms are `3779136` and `10⁵`, and
  `log 3779136 < 22`.
- F3 (L934-947): `h([z_m]) ≤ 10⁴·2²⁴·X`, where `X = max(1, h_F(A))`.
- E4 (L900-905, both branches): `X ≤ max(1, C_cm, Q_R¹⁷)M²⁴`.

Since `X ≥ 1`, `h(J(u)) ≤ (40·10⁴·2²⁴ + 22)·max(1, C_cm, Q_R¹⁷)·M_S(u)²⁴`. At `R = D` and
`S = S_mul` this is `JHeightBound`, with `heightX heightD = max 1 (max C_cm (Q_D¹⁷))` and
`Q_R = R^{R E₀}`. So the `J`-form variants assume steps A1-F3 and nothing else. F4 and the final
numerics become Lean proofs.

**`twelve_mul_ratHeight_le` (VERIFIED).**

- Lean proves it with the standard axioms (BackToU and JHeight compile). The proof never uses
  `u ∉ 𝒞`, so it holds for every `u ∈ ℚ`.
- `f4_check.py` tested 30 values of `u` (the six contact values and 24 others). The largest value
  of `12h(u) − h(J(u))` was 49.1, against the bound 450. Every cancellation
  `gcd(57600F_h², G_h⁶)` divides `C₀`.
- It is not N5's literal F4 (`h(u) < h(j) + 74`). It is a different inequality, proved, and
  stronger for `h(u) > 34`.

**Strength.** `JHeightBound` implies `SixContactMin` in Lean, so as a Prop it is the stronger
hypothesis. Its trust statement is the shorter one: F4 is removed. lit-adopt's docstring says
this correctly.

## 5. The notes' claims

**wk-cr3 §1.3.**

- Lemma (ii) holds (VERIFIED). `{1, 5}` is a subgroup of `(ℤ/8)^×`, and both `|β| ≡ 7` and
  `d/|β| ≡ 3` lie outside it. So each has a prime `≡ 3` or `7`, and these primes are distinct
  because `d` is squarefree.
- Lemma (i) holds when `v_p(β) = 1`. Then `v_p(β(β²s⁴ − 1))` is `1` or `3 − 4k`, which is odd.
- The table's Kriz row (arXiv:2002.04767, a 2-converse that covers every CR₃ curve) is marked
  "preprint, status not checked". The conclusion "only TYZ among refereed theorems" therefore
  depends on that status (**N2**). If Kriz is refereed, a second route exists: `#Sel₂ = 8` with
  2-parity gives `Sel_{2^∞}` corank 1, the 2-converse gives `ord = 1`, and `GrossZagier` finishes.
  That route would avoid Proposition N (SPECULATIVE; not checkable offline).

**wk-cr3 §3 (faithfulness table).**

- The `FunctionalEquation5` row says "exactly the standard functional equation … true as stated:
  yes". That is wrong for the draft (§1.2) and right after the restriction.
- The `GrossZagierKolyvagin` row cites Murty–Murty, as in §3.1 (**N1**).
- The other rows hold.
- The L-series paragraph agrees with §2: `Δ = 64d⁶` and `c₄ = 48d²`, the model is minimal, and
  reduction is additive at 2 and at `p | d`.

**wk-h §1 (classification).**

- The counts W 15, G 8, R 3, B 10 add up to h-trust's 36 labels (VERIFIED).
- The note's rule says "a step with a W input whose own argument is new is classed G or B". That
  rule is not applied to three steps, each of which contains a passage new in N5 (h-trust §2.1):
  - A9: the Milne paragraph, L564-570, and the centralizer step;
  - C3: the lemma `lem:de-rham-descent`, L734-737 and L10938-11000;
  - C9: the Li–Shimura sentence, L768-772, with repairs R-C9-1 to R-C9-3.
- The G steps B1-B3 and D2-D4 also carry the repository repairs R1-R3, which the R class does not
  count.
- So "15 well-known" overstates. Roughly 12 steps are W, and three are mixed (**N3**). This does
  not change wk-h's verdict, which rests on statability.

**wk-h §3 and §5.**

- §3.3's theta-vacuity argument holds (VERIFIED). `t ↦ [3779136t⁴s³⁶ : (9s⁸ + t⁸)⁵]` has no common
  zero, so it is a degree-40 morphism of `P¹`, and `h(t) = h(j)/40 + O(1)` (STANDARD).
- The absence claims were spot-checked by grep of Mathlib (VERIFIED). There is no Tate module,
  Faltings height, newform, Chebotarev, Skolem–Noether, Hodge–Tate, upper numbering or Néron
  model.
- The obstacle (§5) is stated correctly.
- §4.3's fake-model argument for Tier 2 is plausible but was not checked (SPECULATIVE, as wk-h
  marks it).

## 6. lit-adopt against the drafts (VERIFIED, log Steps 9 and 11)

The files compared are `CR3Literature.lean`, `JHeight.lean` and `MainLiterature.lean` at
`9367dfa6`.

**Bodies.** Every Prop and definition body is identical to the draft, apart from the two listed
changes:

- `FunctionalEquation5` gains `0 < s.re → s.re < 2 →`;
- `GrossZagierKolyvagin` is renamed `GrossZagier`, with its docstring supplier changed.

The identical bodies are `IsLContinuation`, `completedL`, `TYZRow5b`, `RootNumberVanishing`,
`HeckeContinuation`, `TYZThm35ReadingA`, `T5aCl`, `Admissible5aNat`, `Jmap`, `Fh`, `Gh`, `C0`,
`heightX` and `JHeightBound`.

**Other deviations.** All are cosmetic or forced, and all are listed in `.fleet/lit-adopt.md`:

- namespaces and docstrings;
- imports;
- `SixContactMinAt` dropped, so that `sixContactMin_of_jHeightBound : JHeightBound Mult.S_mul →
  SixContactMin`;
- line rewraps.

**Variants.** The three variants in `MainLiterature.lean` are one-line compositions through
`…_of_sixContactMin_certifiedRankTYZClRk`. Concatenated and compiled here, they depend only on
`propext`, `Classical.choice` and `Quot.sound`.

## 7. Repairs

| # | File | Declaration / section | Repair | Blocks adoption? |
| --- | --- | --- | --- | --- |
| L1 | `scratch/wk-cr3/Literature.lean` → `CR3Literature.lean` | `FunctionalEquation5` | restrict to `0 < Re s < 2` | yes; **done** on lit-adopt |
| L2 | same | `GrossZagierKolyvagin` | rename `GrossZagier`; supplier BFH 1990 / Waldspurger / Friedberg–Hoffstein 1995 | citation only; **done** |
| N1 | `docs/research/wk-cr3.md` | §0, §1.2, §3 table | `FunctionalEquation5` true only on the strip; drop Murty–Murty | no |
| N2 | `docs/research/wk-cr3.md` | §0, §1.3 conclusion | "only TYZ among refereed theorems" is conditional on Kriz arXiv:2002.04767 being unrefereed; check its status | no |
| N3 | `docs/research/wk-h.md` | §1 table and counts | reclass A9, C3, C9 as mixed W+G (new N5 passages); mention R1-R3 inside B1-B3, D2-D4 | no |
| O1 (optional) | `CR3Literature.lean` | module docstring | cite rv-lit §2 for the match of `WeierstrassCurve.LSeries` with the standard L-function, including split/nonsplit reduction at 2 and 3 | no |

## 8. Scripts (`scratch/rv-lit/`)

| File | Checks | Outcome |
| --- | --- | --- |
| `an_check.py` | Mathlib recipe vs `ellan`, 29 curves, `n ≤ 300` | 0 mismatches |
| `fe_check.py` | conductor and root number (30 `d`), `Λ(2−s) = −Λ(s)` at 9 points, `L(C_d, 2)` | 0 failures; `L(C_d, 2) ≠ 0` |
| `tyz_sample.py` | `T5aCl`, `T5bCl` vs analytic rank, 30 `d` | 0 violations |
| `f4_check.py` | `12h(u) ≤ h(J(u)) + 450` and `c ∣ C₀`, 30 `u` | holds; maximum 49.1 |
| `Probe.lean` | curve parsing, `Γ(0) = 0`, `analyticOrderAt` junk | compiles |
| `log.md` | step log | — |
