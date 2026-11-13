# wk-cr3: reducing CR₃ to well-known theorems

Status: research note (task wk-cr3, 2026-11-11, base `66e9ce28`). Goal of the wave: replace the
hypothesis CR₃ by Lean Props that are faithful statements of well-known published theorems, and
prove CR₃ from them in Lean. This note lists the candidates (§1), drafts the Props in Lean (§2),
checks faithfulness (§3), and gives the proof plan and costs (§4). The Lean draft is
`scratch/wk-cr3/Literature.lean`; the log and scripts are in `scratch/wk-cr3/`. No file under
`ZInQKernel/` was edited.

Marks: **VERIFIED** (checked against a source quoted in the repository, by exact computation, or by
Lean), **STANDARD** (published theorem, with a reference; locators not read here are flagged
UNVERIFIED), **SPECULATIVE** (an assessment or idea).

## 0. Verdict

**Recommended reduction.** Replace `CertifiedRankTYZClRk` by three Props over Mathlib's L-series of
an elliptic curve (`WeierstrassCurve.LSeries`, new in Mathlib v4.35.0):

1. `GrossZagierKolyvagin`: for **every** elliptic curve `E/ℚ`, if `L(E, s)` has a simple zero at
   `s = 1`, then `E(ℚ)` has a point of infinite order. This is the classical theorem of
   Gross–Zagier (with modularity and an auxiliary-twist nonvanishing theorem; Kolyvagin adds
   `rank = 1`).
2. `FunctionalEquation5`: for squarefree `d ≡ 5 (mod 8)`, `Λ(2 − s) = −Λ(s)` with
   `Λ(s) = (32d²)^{s/2}(2π)^{−s}Γ(s)L(C_d, s)`. This is Hecke/Deuring's functional equation for the
   CM curve `C_d`, with conductor `32d²` and Birch–Stephens's root number `−1`.
3. `TYZRow5b`: for squarefree `d ≡ 5 (mod 8)` with `T5bCl d = 1`, `L(C_d, s)` has an entire
   continuation with order at most 1 at `s = 1`. This is "`𝓛(n) ≠ 0`" for TYZ's `(7, 3)` row.

Lean proves `TYZRow5b → FunctionalEquation5 → GrossZagierKolyvagin → CertifiedRankTYZClRk`, and
`FrozenTarget` from `SixContactMin` and the three Props. The draft compiles with no `sorry` and
only the axioms `propext`, `Classical.choice` and `Quot.sound` (VERIFIED, §2.4).

**What remains assumed.** Props 1 and 2 are textbook theorems. Prop 3 is the only one that is not a
printed sentence. It is reading A of TYZ's Theorem 3.5(2) (`n ≡ 5`, row `(7, 3)`, contrapositive).
TYZ's printed Theorem 1.2 is false as written (nt-tyz §1.4). The only printed statement of reading A
is Smith's unrefereed Theorem 2.1. A complete proof from unambiguous TYZ statements is Proposition N
(nt-tyz §4; two model reviews, no human review). So the reduction makes the TYZ input
**smaller** but does not remove Proposition N. What CR₃ assumed before was TYZ, Proposition N,
Gross–Zagier, Birch–Stephens and the match of definitions, all bundled in one statement written
for this project. Now TYZ with Proposition N is one Prop, `TYZRow5b`, whose conclusion is a
standard analytic statement. The Gross–Zagier and root-number steps become separate Props, each
a recognizable published theorem.

**Most serious obstacle.** No refereed text states `TYZRow5b`. The journal version of TYZ (Asian
J. Math. 21 (2017)) and Tian's ICM 2022 article have not been read by anyone here.

**No published theorem with prime restrictions can replace TYZ** for any slot choice (VERIFIED,
§1.3). Every `d` that CR₃ or the slot construction uses has at least two primes `≢ 1 (mod 8)`, and
`ω(d)` is unbounded.

**Costs.** Cheap win: adopt `Literature.lean` as a new hypothesis file with a main-theorem variant
(done in scratch; about a day to integrate and review). Medium: Lean lemmas that pin down Mathlib's
L-series on `C_d`, so the definitions cannot hide junk values (§4.2). Bigger: a refereed source for
`TYZRow5b`; this is a literature task, not Lean work. Proving any of the three Props in Lean is out
of reach.

## 1. Candidates

### 1.1 (a) Tian–Yuan–Zhang for `n ≡ 5 (mod 8)`, in a true form

TYZ = Y. Tian, X. Yuan, S.-W. Zhang, *Genus periods, genus points and congruent number problem*,
Asian J. Math. 21 (2017), 721–774, read only as arXiv:1411.4728v1 (nt-tyz §1.1). Every statement
below is from nt-tyz §1.2–1.4, which quotes the TeX source with line numbers.

- **Theorem 1.2 as printed is false** (VERIFIED in nt-tyz §1.4 by exact computation: `n = 26565`
  and `n = 33117` have rank 3, yet the second sum under the printed convention "all `d_i > 1`" is
  odd). It cannot be cited, not even through a consequence.
- **Reading A** (`d₁ = 1` admitted) is the true form (nt-tyz §1.3–1.4). For `n ≡ 5` it says: if
  `2^{−ρ(n)}𝓛(n)` is even, then `T_5a(n)` and `T_5b(n)` are both even. Theorem 3.5(2) as printed
  omits "all `d_i > 1`", so reading A is a *permitted* reading of a printed statement (VERIFIED,
  nt-tyz §1.2). It is not the only permitted one. TYZ's own proof needs reading A in
  Proposition 3.4 (L2077).
- **What a faithful citation of reading A still needs from Proposition N.** TYZ's printed proof of
  Theorem 3.5(2) reads both brackets off Proposition 3.4. That proposition's statement has the same
  ordering and `d₁ = 1` ambiguity, and its proof is a sketch: an induction over all classes at once,
  including a one-line multiplicity cancellation (nt-tyz §2.3). Its last step S4–S6 is sound and
  separates the `(7, 3)` bracket (VERIFIED, nt-tyz §2.3). So citing "TYZ Theorem 3.5(2), reading A"
  rests on Proposition 3.4 in reading A. Proposition N replaces exactly that input by Lemma N1
  (Theorem 1.1 read as set partitions) and Lemma N2 (the coefficients `c_n(e) ≡ 𝓛(n/e) mod 2`),
  plus the implicit facts F3 and F5. Everything else in Proposition N's proof is TYZ's own argument.
  **Smallest gap: Lemmas N1, N2 and fact F5,** about one page of new argument (nt-tyz §4.3–4.4).
- **Row 5a as an alternative** (SPECULATIVE, rejected). The first congruence of printed
  Theorem 1.2 ("`T_5a(n)` odd ⟹ `2^{−ρ}𝓛(n)` odd") has an unambiguous statement. But it is a
  conjunct of a false printed theorem, and TYZ prove it through Proposition 3.4 in reading A as well.
  The slot curves control `T_5b`, not `T_5a`: on 12 minimal-Selmer curves with a class `|a| ≡ 3 (4)`,
  `T5b = 1` on 12 and `T5a = 1` on only 7. A redesign around classes `|a| ≡ 1 (4)` would need an
  extra condition, since `T5a = 1` held on 9 of 11 such curves (VERIFIED, `row5a_check.py`, 30
  curves). No gain.
- **TYZ Corollary 1.4** restricts the primes of `n` (pc-audit §4.5). It is excluded by §1.3.

### 1.2 (b) Analytic rank one, then a point

- **Analytic rank one.** `TYZRow5b` (`ord ≤ 1`) together with the root number (`ord` odd, or
  `L(C_d, 1) = 0`) gives `ord_{s=1} L(C_d, s) = 1`. TYZ define `𝓛(n) = 0` exactly when `ord > 1`
  (L318–345, nt-tyz I7), so TYZ's conclusion `𝓛(n) ≠ 0` *is* `ord ≤ 1`.
- **The L-function.** Mathlib v4.35.0 defines `WeierstrassCurve.LFunction` and
  `WeierstrassCurve.LSeries` (`Mathlib/AlgebraicGeometry/EllipticCurve/LFunction.lean`) for any
  Weierstrass curve over a number field. Each prime gets the local factor of the minimal model
  (`Reduction.lean`): `1 − a_p T + p T²` with `a_p = p + 1 − #W̃(𝔽_p)` for good reduction, `1 ∓ T` for
  split or nonsplit multiplicative reduction, `1` for additive reduction. These are Silverman's
  definitions (VERIFIED by reading). So no point counting needs to be added to the fork.
- **Analytic continuation.** For `C_d` it is classical: `C_d` has CM by `ℤ[i]`, so `L(C_d, s)` is a
  Hecke L-function of `ℚ(i)` (Deuring; STANDARD), entire, with the functional equation of §2.2.
  Mathlib has no Hecke L-functions, so continuation enters as part of a Prop. The order of vanishing
  is Mathlib's `analyticOrderAt` (`Mathlib/Analysis/Analytic/Order.lean:49`), applied to an entire
  `F` that agrees with the series on `Re s > 3/2`. Such an `F` is unique; Lean proves this
  (`IsLContinuation.eq`).
- **Point of infinite order.** Gross–Zagier, Invent. Math. 84 (1986), 225–320, with an imaginary
  quadratic `K` satisfying the Heegner hypothesis and `L(E^K, 1) ≠ 0`: Bump–Friedberg–Hoffstein,
  Invent. Math. 102 (1990), 543–618, or Murty–Murty, Ann. of Math. 133 (1991) (STANDARD; exact
  theorem numbers UNVERIFIED, as in cr3-trust D2–D3). Modularity: for `C_d`, Shimura 1971 (CM); for
  all `E/ℚ`, Breuil–Conrad–Diamond–Taylor, J. Amer. Math. Soc. 14 (2001). Kolyvagin (Math. USSR Izv.
  32 (1989)) gives `rank = 1`, which is not needed. The general statement "analytic rank one implies
  rank one" (Gross–Zagier–Kolyvagin) is among the best-known theorems of the subject. So the Prop
  is stated for every `E/ℚ`, not only for `C_d`.

### 1.3 (c) Other published theorems, and the slot choice

**Which `d` occur** (VERIFIED from `RouteK/RankDL.lean` and slot-k §1–2). Pole completeness uses
two curves, `C_{d₁}` and `C_{d₁|θ|}`, with `d₁ ≡ 5 (mod 8)` squarefree, `β | d₁` and
`|β| ≡ 7 (mod 8)` (`Inputs.mod_β`), and a Selmer certificate for `β`. The primes of `β` come from the
instance, and `ω(β)` is unbounded at the test site (slot-k §1.3).

**Lemma (VERIFIED, elementary).** (i) If `C_d` has a rational point with `x ∈ βℚ*²`, then every prime
of `β` divides `sqf(d)`. (ii) If `d ≡ 5 (mod 8)` and `|β| ≡ 7 (mod 8)` divides `d`, then `d` has at
least two primes `≢ 1 (mod 8)`.

*Proof.* (i) By cr3-map-literature R1, `d ∈ β(β²s⁴ − 1)ℚ*²`. For `p | β`: if `v_p(s) ≥ 0` then
`v_p(β(β²s⁴ − 1)) = 1`; if `v_p(s) = −k < 0` it is `1 + 2 − 4k`. Both are odd. (ii) Primes `≡ 1, 5`
generate only the classes `{1, 5}`. So `|β| ≡ 7` has a prime `≡ 3` or `7`, and so does
`d/|β| ≡ 3`. ∎

So no choice of slots or multiplier makes the primes of `d` "all `≡ 1 (mod 8)` but one". In
general (two instance primes `≡ 3 (mod 8)` in `β`) not even a change of the class of `β` helps.

| Theorem | Hypotheses | Covers the CR₃ curves? |
| --- | --- | --- |
| Heegner (1952), Birch, Stephens, Monsky (Math. Z. 204 (1990)) | one to three odd primes in fixed classes | no: `ω` unbounded (pc-audit §4.5) |
| Tian, *Congruent numbers and Heegner points*, Cambridge J. Math. 2 (2014) | all odd primes `≡ 1 (mod 8)` but one, plus a 4-rank condition (as recorded in cr3-map-literature C3 and pc-audit §4.5; text not read here) | no: Lemma (ii) |
| TYZ Corollary 1.4 | conditions on the primes `≡ 3 (mod 4)` of `n` (pc-audit §4.5) | no: arbitrary primes of `β` |
| TYZ reading A (§1.1) | `T_5a` or `T_5b` odd | yes, every curve (tyz-5b Thm 5.1, Lean `det_M5b_eq_one`), but not a printed true sentence |
| Smith, arXiv:1603.08479, Thm 2.1 | reading A, rows separated | yes, but unrefereed |
| Smith, arXiv:1702.02325 | density of 2^∞-Selmer coranks | no: densities, and corank one still needs a converse |
| Kriz, arXiv:2002.04767, Thm 10.13 (2-converse) with the corank lemma | `Sel_{2^∞}` corank one | yes, every CR₃ curve (slot-k §1.2), but a preprint (publication status not checked) |
| Coates–Wiles, Rubin | `L(1) ≠ 0` | wrong direction (rank 0) |
| Monsky 2-parity; Dokchitser–Dokchitser, Ann. of Math. 172 (2010) | none | gives corank parity, never a point |

**Conclusion (c).** Among refereed theorems, only TYZ covers the curves the construction needs, and
only through reading A of a row `b`. In each class `n ≡ 5, 6, 7` the second sum of printed
Theorem 1.2 has two types of term: one where `d₁ > 1` is forced (`(7, 3)`, `(7, 2)`, `(5, 3)`) and
one where `d₁ = 1` is possible and the convention matters (`(5, 1)`, `(6, 1)`, `(7, 1)`). The
enumeration of classes is VERIFIED arithmetic. So the forced row is printed only inside a sum
together with an ambiguous row. Isolating it needs reading A, or an argument like Proposition N.
Changing the class of `d` therefore does not help (SPECULATIVE for `n ≡ 6, 7`, whose printed
statements were not tested against counterexamples).

## 2. Lean statements (draft `scratch/wk-cr3/Literature.lean`)

### 2.1 Definitions

```lean
/-- `F` is an entire continuation of `L(E, s)` from `Re s > 3/2`. -/
def IsLContinuation (E : WeierstrassCurve ℚ) (F : ℂ → ℂ) : Prop :=
  Differentiable ℂ F ∧ ∀ s : ℂ, 3 / 2 < s.re → F s = E.LSeries s

theorem IsLContinuation.eq {E F G} (hF : IsLContinuation E F) (hG : IsLContinuation E G) : F = G

noncomputable def completedL (N : ℕ) (F : ℂ → ℂ) (s : ℂ) : ℂ :=
  (N : ℂ) ^ (s / 2) * (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * F s
```

`E.LSeries` is Mathlib's. `T5bCl` and `gCl` are the fork's (`Rank5b/Sec3/RedeiStatement.lean:49,
55`). The draft adds `T5aCl` and `Admissible5aNat` for the row-5a sum.

### 2.2 The Props

```lean
def GrossZagierKolyvagin : Prop :=
  ∀ (E : WeierstrassCurve ℚ), E.IsElliptic → ∀ F : ℂ → ℂ, IsLContinuation E F →
    analyticOrderAt F 1 = 1 → ∃ P : E.toAffine.Point, ¬IsOfFinAddOrder P

def FunctionalEquation5 : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → ∀ F : ℂ → ℂ,
    IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F →
      ∀ s : ℂ, completedL (32 * d ^ 2) F (2 - s) = -completedL (32 * d ^ 2) F s

def TYZRow5b : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → T5bCl d = 1 →
    ∃ F : ℂ → ℂ, IsLContinuation (shortCurve (-(d : ℚ) ^ 2)) F ∧ analyticOrderAt F 1 ≤ 1
```

Variants in the draft:

- `RootNumberVanishing`: `F 1 = 0`. It is weaker than `FunctionalEquation5` and Lean derives it from
  that Prop.
- `HeckeContinuation`: `∃ F`, for every `d ≠ 0`.
- `TYZThm35ReadingA`: `ord ≥ 2 → T5aCl d = 0 ∧ T5bCl d = 0`. This is the literal shape of reading A,
  with "`𝓛(n) = 0`" in place of "`2^{−ρ}𝓛(n)` even". Lean derives `TYZRow5b` from it and
  `HeckeContinuation` (`tyzRow5b_of_readingA`). So TYZ may be cited in its own shape (both rows) at
  the price of one more Prop, Hecke's continuation.

### 2.3 Proofs in the draft

- `rootNumberVanishing_of_functionalEquation`: at `s = 1`, `Λ(1) = −Λ(1)`; `Γ(1) = 1` and the
  powers are nonzero.
- `analyticOrder_eq_one`: `ord ≤ 1` and `F 1 = 0` (with `F` analytic, by `analyticOrderAt_ne_zero`)
  give `ord = 1`.
- `certifiedRankTYZClRk_of_literature : TYZRow5b → RootNumberVanishing → GrossZagierKolyvagin →
  CertifiedRankTYZClRk`. It applies `GrossZagierKolyvagin` to `shortCurve (−d²)`, using
  `shortCurve_isElliptic`.
- `frozenTarget_of_sixContactMin_literature : SixContactMin → TYZRow5b → FunctionalEquation5 →
  GrossZagierKolyvagin → FrozenTarget`, through
  `exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk`
  (`RouteK/RankVariants.lean:69`).

From `CertifiedRankTYZClRk`, the existing chains of cr3-trust §0.2 give every other form:
`Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk`, `certifiedRankRk_of_certifiedRankTYZRk`,
`certifiedRankDLRk_of_certifiedRankTYZRk`, `certifiedRankDLAdmRk_of_certifiedRankDLRk`,
`certifiedRank_of_certifiedRankRk'`. So targeting `CertifiedRankRk` or `CertifiedRankDLAdmRk` instead
gains nothing: the TYZ Prop is needed in the same strength. Its hypothesis `T5bCl d = 1` is what
the literature states, and the narrower forms only add the project's bookkeeping.

### 2.4 Compile status (VERIFIED)

The whole file compiles with `lake env lean`, run against the prebuilt oleans of a checkout at
`520e27e5`. That commit differs from the base only in `KERNEL_PLAN.md` and `README.md`. There are no
errors and no `sorry`. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for
`IsLContinuation.eq`, `certifiedRankTYZClRk_of_literature`, `tyzRow5b_of_readingA`,
`rootNumberVanishing_of_functionalEquation` and `frozenTarget_of_sixContactMin_literature`
(`scratch/wk-cr3/out_literature.txt`).

## 3. Faithfulness

| Prop | Published source | Exactly, or a consequence? | True as stated? | Gap |
| --- | --- | --- | --- | --- |
| `GrossZagierKolyvagin` | Gross–Zagier 1986 + BFH 1990 / Murty–Murty 1991 + BCDT 2001; Kolyvagin 1989 for `rank = 1` | consequence: "`ord = 1 ⟹ rank = 1`" specialized to "some point of infinite order"; `∀ F` is harmless because the continuation is unique (`IsLContinuation.eq`) and exists (BCDT + Hecke) | yes (STANDARD) | exact theorem numbers UNVERIFIED (cr3-trust §2.4); faithfulness of Mathlib's `LSeries` (below) |
| `FunctionalEquation5` | Deuring/Hecke (functional equation of the Hecke L-function); conductor `32d²` for odd squarefree `d`; Birch–Stephens 1966 (root number) | exactly the standard functional equation `Λ(2 − s) = wΛ(s)` with `w = −1` | yes (STANDARD); conventions checked on 20 curves (below) | locators UNVERIFIED; the identification `L(C_d, s) = L(ψ, s)` is Deuring's theorem, not Lean |
| `RootNumberVanishing` | consequence of the previous row | consequence (Lean-proved) | yes | none beyond the previous row |
| `TYZRow5b` | TYZ Thm 3.5(2), `n ≡ 5`, reading A, row `(7, 3)`, contrapositive, weakened from "`2^{−ρ}𝓛` odd" to "`𝓛 ≠ 0`"; Smith Thm 2.1 (unrefereed) | consequence of reading A, never stronger. But reading A is one of the readings the printed statement allows, not the only one (§1.1) | yes: Proposition N (nt-tyz §4; rv-nt-tyz, rv-prop-n, both "holds"), and numerical checks: every `T5b`-odd sample has analytic rank 1 (nt-tyz §1.4, cr3-trust A6, rv-prop-n §5) | **Proposition N** (Lemmas N1, N2, F5), or Proposition 3.4 in reading A; the match `T5bCl` = TYZ's `T_5b` ([M3], cr3-trust A1–A2); TYZ read in arXiv v1 only |
| `TYZThm35ReadingA` | TYZ Thm 3.5(2), `n ≡ 5`, reading A | consequence: hypothesis weakened to `𝓛(n) = 0` (nt-tyz F6) | yes (Proposition N, first sentence) | as `TYZRow5b`; plus `T5aCl` is new and not reviewed |
| `HeckeContinuation` | Deuring, Hecke | exactly | yes | none in substance |

**The L-series definition** (VERIFIED: by reading, and by PARI on 20 curves). The model
`y² = x³ − d²x` has `Δ = 64d⁶` and `c₄ = 48d²`. For odd squarefree `d` it is minimal at every
prime (`v_p(Δ) < 12`), has good reduction for `p ∤ 2d`, and has additive reduction at 2 and at
`p | d` (`v_p(c₄) > 0`). So Mathlib's Euler factor is `1 − a_pT + pT²` with
`a_p = p + 1 − #C_d(𝔽_p)` for good `p`, and `1` at bad `p`. That is the standard `L(C_d, s)`.
`conventions_check.py` confirms the following for 20 squarefree `d ≡ 5 (mod 8)` below 4000, with no
failure (`out_conventions_check.txt`):

- the conductor is `32d²` and the root number is `−1`;
- the given model is minimal;
- the Kodaira types are III at 2 and I₀* at `p | d` (additive);
- `ellap = 0` at the bad primes, and `ellap(p) = p + 1 − #C_d(𝔽_p)` for the good `p < 40`.

The normalization is arithmetic: centre `s = 1`, absolute convergence for `Re s > 3/2` by Hasse's
bound (STANDARD), and `Λ(s) = N^{s/2}(2π)^{−s}Γ(s)L(s)`. Residual risk: `WeierstrassCurve.LSeries`
is new in Mathlib (2026), and no Mathlib lemma yet connects it to point counts. A junk value would
make the Props false, not vacuous, because `TYZRow5b` asserts that `F` exists. Tier-2 lemmas
(§4.2) would close this risk.

**Smallest gap left.** One unrefereed repository argument, Proposition N's Lemmas N1–N2 with fact
F5, standing in for TYZ's Proposition 3.4. Alternatively, one interpretive step: reading A of the
printed Theorem 3.5(2). Everything else is published.

## 4. Lean plan and costs

### 4.1 Cheap win (about a day of integration; SPECULATIVE estimate)

1. Move `Literature.lean` to `ZInQKernel/Hypotheses/CR3Literature.lean`. Keep the Props as `def …
   : Prop` with trust docstrings (no `axiom`).
2. Add the main-theorem variant `…_of_sixContactMin_tyzRow5b_functionalEquation_grossZagier` to
   `RouteK/RankVariants.lean` or the new file, and register it in `scripts/print_axioms.lean`.
3. Update cr3-trust §1 so that Parts C4 and D become the two textbook Props, and the trust
   statement for CR₃ reads "TYZ row 5b (with Proposition N) + functional equation +
   Gross–Zagier".

No new mathematics is needed in Lean; the draft already proves everything with the standard axioms.

### 4.2 Medium investment (weeks; SPECULATIVE estimate)

Make the L-series definition auditable inside Lean:

- the model `shortCurve (−d²)` is minimal at every prime, with good reduction for `p ∤ 2d` and
  additive reduction at `p | 2d`;
- hence the coefficient of `p` in `(shortCurve (−d²)).LFunction` is `p − #{(x, y) ∈ 𝔽_p² : y² = x³ − d²x}`
  for `p ∤ 2d`, and `0` for `p | 2d`;
- `a_p = 0` for `p ≡ 3 (mod 4)` (the involution `x ↦ −x`; elementary).

Optionally, add Hasse's bound for `C_d` (Jacobi sums over `ℤ[i]`), which gives `LSeriesSummable` on
`Re s > 3/2`. These lemmas do not change what is assumed. They remove the risk that a Mathlib
definition differs from the textbook one.

### 4.3 Bigger investment

- **Literature, not Lean.** Find a refereed statement of `TYZRow5b`, or of reading A: read the
  journal version of TYZ, or Tian's ICM 2022 article (EMS Press, open access), or publish
  Proposition N. Any of these would turn `TYZRow5b` into a citation.
- **Lean, out of reach.** Proving `HeckeContinuation` or `FunctionalEquation5` needs Hecke
  L-functions of `ℚ(i)` and Deuring's identification of `L(C_d, s)`; that is months or more.
  Gross–Zagier and TYZ need Heegner points, Shimura curves and Waldspurger's formula; that is not
  feasible.

### 4.4 What remains assumed after the cheap win

`SixContactMin` (unchanged), `TYZRow5b`, `FunctionalEquation5` and `GrossZagierKolyvagin`. Of
these, the last two are textbook theorems; the first rests on TYZ together with Proposition N.

## 5. Scripts and outputs (`scratch/wk-cr3/`)

| File | Purpose | Outcome |
| --- | --- | --- |
| `Literature.lean` | the Props and the reductions | compiles; standard axioms (`out_literature.txt`) |
| `conventions_check.py` | conductor, root number, minimality, reduction types, `a_p` on 20 curves | 0 failures (`out_conventions_check.txt`) |
| `row5a_check.py` | class of the Selmer generator against `T5a`, `T5b` on 30 minimal-Selmer curves | `|a| ≡ 3 (4)` ⟹ `T5b = 1` (12/12); `|a| ≡ 1 (4)`: `T5a = 1` on 9/11 (`out_row5a_check.txt`) |
| `log.md` | step log | — |

## Note (2026-11-11, after rv-lit)

- §0, §2.2 and §3: `FunctionalEquation5` as drafted (for every `s`) is false in Lean. Mathlib's
  `Complex.Gamma` is 0 at `0, −1, −2, …`, so at `s = 0` the identity forces `L(C_d, 2) = 0`. The
  adopted form (`ZInQKernel/Hypotheses/CR3Literature.lean`) holds for `0 < Re s < 2` only; it is a
  consequence of the functional equation and suffices, since the proof uses `s = 1`. The adopted
  Gross–Zagier Prop is `GrossZagier`. Its source for `L(E^K, 1) ≠ 0` is Bump–Friedberg–Hoffstein
  1990 (through Waldspurger) or Friedberg–Hoffstein 1995; Murty–Murty 1991 concerns derivatives
  (rv-lit N1).
- §1.3: "only TYZ among refereed theorems" assumes that Kriz's 2-converse (arXiv:2002.04767) is
  unrefereed; its publication status was not checked (rv-lit N2).
