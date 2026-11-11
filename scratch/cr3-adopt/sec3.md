## 3. Draft docstrings (lines ≤ 100 characters; repaired after rv-cr3-trust, applied by cr3-adopt)

**`ZInQ.CertifiedRank`** (`ZInQKernel/Hypotheses/CertifiedRank.lean`): replace the docstring of the
definition.

```lean
/-- **Hypothesis CR₃** (certified rank). Let `d > 0` be squarefree with `d ≡ 5 (mod 8)`, and let
`a` be a squarefree (signed) divisor of `d` with `|a| ≡ 7 (mod 8)`. If the system `Σ(𝒞_d)` of the
configuration of `d` has exactly 8 solutions (dimension 3) and one of them has first coordinate the
class of `a` (`a₀ = [a < 0]`, `a₁ = 0`, `u_p = [p ∣ a]`), then the congruent number curve
`C_d : y² = x³ − d²x` has a rational point `(x, y)` with `x ≠ 0` and `x ∈ a ℚ*²`.

**Trust statement.** CR₃ is not proved in Lean. Lean derives it from `RouteK.Rank.CertifiedRankRk`
(`certifiedRank_of_certifiedRankRk'`), and that from `RouteK.Rank.CertifiedRankTYZClRk`
(`Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk`, `certifiedRankRk_of_certifiedRankTYZRk`).
The latter says: for squarefree `d ≡ 5 (mod 8)` with odd genus sum of class numbers `T5bCl d`,
`C_d(ℚ)` has a point of infinite order. Its proof is published mathematics, one short repository
argument, and the match of the Lean definitions with TYZ's quantities (model reviews);
`docs/research/cr3-trust.md` lists every step with its supplier:

* *Tian–Yuan–Zhang* (Y. Tian, X. Yuan, S.-W. Zhang, *Genus periods, genus points and congruent
  number problem*, Asian J. Math. 21 (2017), 721–774; read in arXiv:1411.4728v1 only):
  Theorem 3.5 (first assertion), Theorem 3.3, Proposition 3.2, Lemmas 2.8, 3.16, 3.18, 3.21,
  Proposition 2.3 and the recursion of §3.1. Their proofs use Waldspurger's formula and the
  Gross–Zagier formula of Yuan–Zhang–Zhang. TYZ's Theorem 1.2 is not cited: as printed (all
  `d_i > 1`) it is false (`docs/research/nt-tyz.md` §1.4).
* *Proposition N* (`docs/research/nt-tyz.md` §4; model reviews `docs/research/rv-nt-tyz.md` and
  `docs/research/rv-prop-n.md`): from these inputs, if the `(7, 3)` genus sum `T_5b(d)` is odd
  then TYZ's `𝓛(d) ≠ 0`, so `ord_{s=1} L(C_d, s) ≤ 1`, and the root number `−1` (Birch–Stephens)
  gives `= 1`. It replaces TYZ's Proposition 3.4 by a direct parity count (Lemmas N1, N2). Not
  refereed.
* *Gross–Zagier* (Invent. Math. 84 (1986)), with an imaginary quadratic field satisfying the
  Heegner hypothesis and `L(C_d^K, 1) ≠ 0` (Bump–Friedberg–Hoffstein): analytic rank one gives a
  point of infinite order. `C_d` is modular since it has CM (Deuring, Shimura). Neither BCDT nor
  Kolyvagin's MPIM preprint is needed; Kolyvagin's published papers enter only inside
  Tian–Yuan–Zhang.

Everything else is proved in Lean: Rédei's formula (`RouteK.Redei.redeiFormula`, which turns
`T5bCl` into Rédei's bits `T5b`), Theorem 3.6 and Corollary 4.4 of `docs/research/tyz-5b.md`
(`RouteK.Rank5b.det_M5b_eq_T5b`, `det_M5b_eq_one`: the premises here give `T5b d = 1`),
Proposition 0 (`RouteK.Selmer.prop0Statement`: `Σ(𝒞_d)` is `Sel₂(C_d)`), Mordell–Weil for `C_d`
(`RouteK.Rank.fg_points`), and the step from a point of infinite order and `#Sel₂(C_d) = 8` to a
point in the class `a` (`RouteK.Rank.loc_of_mem_sel2_of_infinite_order`; pc-audit RK9).
Kriz's 2-converse (arXiv:2002.04767, Theorem 10.13, a preprint) with the corank lemma is an
alternative route; it is not needed (`docs/research/nt-tyz.md` §5.1). Weaker forms that Lean also
accepts: `RouteK.Rank.CertifiedRankDLRk` and `CertifiedRankDLAdmRk` (only the curves the proof
uses). -/
```

**`RouteK.Rank.CertifiedRankTYZClRk`** (`ZInQKernel/RouteK/Rank/Statements.lean`): the trust
paragraph.

```lean
**Trust statement.** Not proved in Lean. It is Tian–Yuan–Zhang (Asian J. Math. 21 (2017),
721–774, read as arXiv:1411.4728v1): Theorem 3.5 (first assertion) with Theorem 3.3,
Proposition 3.2, Lemmas 2.8, 3.16, 3.18, 3.21 and Proposition 2.3, as completed by Proposition N
(`docs/research/nt-tyz.md` §4, model reviews `docs/research/rv-nt-tyz.md` and
`docs/research/rv-prop-n.md`; not refereed): if `T5bCl d` is odd, TYZ's `𝓛(d) ≠ 0`, and with the
root number `−1` (Birch–Stephens) `ord_{s=1} L(C_d, s) = 1`. Then Gross–Zagier (Invent. Math. 84
(1986)), with an auxiliary imaginary quadratic field (Bump–Friedberg–Hoffstein), gives a point of
infinite order. `T5bCl d` is TYZ's `(7, 3)` genus sum with `g(d_B) = #Cl(ℚ(√−d_B))²`, so no Rédei
formula is needed; TYZ's Theorem 1.2 is not cited (false as printed). Lean derives every other
form of CR₃ from it (the forms with the premise `#Sel₂ = 8` through RK9 and Mordell–Weil,
`certifiedRankTYZ_of_certifiedRankTYZRk'`, `certifiedRankTYZCl_of_certifiedRankTYZClRk'`).
Step-by-step outline: `docs/research/cr3-trust.md`.
```

**`RouteK.Rank.CertifiedRankRk`** (`ZInQKernel/RouteK/Rank/Statements.lean`): the trust paragraph.

```lean
**Trust statement.** Not proved in Lean. Lean derives it from `CertifiedRankTYZClRk`
(`Redei.certifiedRankTYZRk_of_certifiedRankTYZClRk`, `certifiedRankRk_of_certifiedRankTYZRk`):
the premises give `T5b d = 1` by Corollary 4.4 and Theorem 3.6 of `docs/research/tyz-5b.md`
(`det_M5b_eq_one`, `det_M5b_eq_T5b`), and Rédei's formula (`RouteK.Redei.redeiFormula`) makes
that `T5bCl d = 1`. So it rests on Tian–Yuan–Zhang as completed by Proposition N
(`docs/research/nt-tyz.md` §4; model reviews `docs/research/rv-nt-tyz.md`,
`docs/research/rv-prop-n.md`) and on Gross–Zagier with an auxiliary field, exactly as
`CertifiedRankTYZClRk` (see there and `docs/research/cr3-trust.md`). Kriz's 2-converse
(arXiv:2002.04767, Theorem 10.13, a preprint) with the corank lemma is an alternative, not needed.
The step to "every Selmer class comes from a rational point" (pc-audit RK9) is proved in Lean
(`loc_of_mem_sel2_of_infinite_order`, with `fg_points`).
```

## 4. Next steps

- Done: rv-prop-n is read and C1-C3 are [M2]; the drafts of §3 are applied, and the docstrings of
  `CertifiedRankSel`, `CertifiedRank5b`, `CertifiedRankTYZ` and the other CR₃ forms and variants
  are aligned (task cr3-adopt); KERNEL_PLAN.md leads with the TYZ route and lists the new
  variants; the CR₃^5b variant without 22P exists (`Rank5bSec3.lean:51`).
- The network checks of §2.4, items 1-4, 8 and 9, decide whether any statement changes; the rest
  are numbering (SPECULATIVE).
- A human referee (or a reviewer with the source) confirms the three quotations Proposition N is
  sensitive to (rv-prop-n §9): the recursion's coefficient `ε(d₀, d₁)𝓛(d₁)` with `ε = ±1` at
  `(5, 1)`, `(7, 1)`, `(7, 3)`; Lemma 3.21(1), (4); Theorem 3.5's first assertion.
- Optionally drop the older CR₃^5b variant with 22P (`Rank5b.lean:37`).

## Changelog

- 2026-11-11 (task cr3-adopt). Applied every repair of `docs/research/rv-cr3-trust.md` §6:
  - Summary 1, §0.2: `CertifiedRankTYZClRk` implies every form, including `CertifiedRankTYZ`,
    `CertifiedRankTYZCl`, `CertifiedRank5b` (premise `#Sel₂ = 8`) and `CertifiedRankDLAdmRk`; the
    chains of existing theorems are given (checked in `scratch/rv-cr3-trust/Check.lean`). The false
    claim "except the three" is removed here and in the §3 draft for `CertifiedRankTYZClRk`.
  - 14 forms, not 13; §0.1 and §0.3 list the variants `…_sixContactMin_certifiedRank5b`
    (`Rank5bSec3.lean:51`) and `…_sixContactMin_certifiedRankDLAdmRk` (`RankDL.lean:232`); the
    recommendation to add the former is removed; locations rechecked at `81bb5d8f`.
  - D2: the supplier is Bump–Friedberg–Hoffstein (or Waldspurger, or Friedberg–Hoffstein 1995) for
    the central value `L(C_d^K, 1) ≠ 0`; Murty–Murty is the derivative case and is dropped as
    supplier; the level `32d²` question is added to §2.4 item 3. Same change in §2.2 and §3.
  - Review counts after rv-prop-n: C1-C3 [M2] (no human review), A1 [M2], A2 [M3]; §2.1, §2.6 and
    the Summary updated; §3 drafts cite rv-prop-n.
  - B5: the inclusion `ℍ'_{d₀} ⊂ ℍ'_n` is a quoted TYZ fact. B8: one lift `β'` serves all `Z(e)`.
    C3: the `ε`-classes used are `(5, 1)`, `(7, 1)`, `(7, 3)`.
  - D1: Shimura 1971 locator. D3: the conjugation sign `ȳ_K = −ε y_K^σ` with locators (Gross–Zagier
    1986, Gross 1984); both added to §2.4. A5: Mathlib's `Point` law is the chord-tangent law; the
    `Inf` forms avoid it. A6 and Summary 4: on the 6 curves without a found point, `ellrank`'s
    lower bound `1` is not certified. rv-cr3-rank is merged and cited as the supplier of A5 and E3.
  - §3: the "Trust statement" opening of the `CertifiedRank` draft now names the match of the Lean
    definitions (model reviews) besides the repository argument.
  - §4 updated. rv-prop-n's corrections to nt-tyz.md are recorded in a dated note at its end.
