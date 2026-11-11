# rv-cr3-rank: adversarial review of CR₃ in positive-rank form (RK9 and Mordell–Weil for `C_d`)

Reviewed commit: `aa494aae` (branch `wip/rv-cr3-rank`, from `wip/integrate-wave8`), i.e. the work of
cr3-kummer (`ZInQKernel/RouteK/Rank/`, root `RouteK/Rank.lean`), cr3-mw (`ZInQKernel/RouteK/RankMW/`,
root `RouteK/RankMW.lean`) and the integration commit (`RouteK/RankVariants.lean`, KERNEL_PLAN.md,
scripts/print_axioms.lean).

## Verdict

**No blocker.** The three positive-rank hypotheses say exactly "`C_d(ℚ)` has a point of infinite
order" under the stated premises; each is implied by the literature its docstring cites; the Lean
derivations RK9 → CR₃^Sel / CR₃^TYZ / CR₃^TYZ_Cl and Mordell–Weil for `C_d` are genuine (no vacuous
hypotheses, `Sel2` is `Selmer.Sel2`, the curve is `shortCurve (−d²)` everywhere); the build passes
and every `#print axioms` entry is `[propext, Classical.choice, Quot.sound]`. Four non-blocking
remarks (§5) concern docstring precision and one implication worth stating in Lean.

## Build and axioms (item 3)

- `lake build ZInQKernel` at `aa494aae`: `Build completed successfully (9906 jobs)`, no errors, no
  `sorry` warnings (scratch/rv-cr3-rank/build-tail.txt).
- `lake env lean scripts/print_axioms.lean`: 38 `#print axioms` lines, 38 entries, every one exactly
  `[propext, Classical.choice, Quot.sound]` (scratch/rv-cr3-rank/axioms.txt). This includes the three new
  main-theorem variants `…_of_sixContactMin_certifiedRankRk`, `…TYZRk`, `…TYZClRk` and
  `fg_points`, `twoTorsion_card`, `loc_of_mem_sel2_of_infinite_order`,
  `certifiedRank_of_certifiedRankRk'`, `certifiedRankTYZ_of_certifiedRankTYZRk'`,
  `certifiedRankTYZCl_of_certifiedRankTYZClRk'`.
- A scratch file (deleted after use) printed the elaborated statements (§1) and checked that
  `#synth AddCommGroup (shortCurve (-(5:ℚ)^2)).toAffine.Point` is Mathlib's
  `WeierstrassCurve.Affine.Point.instAddCommGroup`, and elaborated without error:

```lean
example (h : ZInQ.RouteK.Rank.CertifiedRankTYZRk) : ZInQ.RouteK.Rank.CertifiedRankRk := by
  intro d hd5 hsq h8 ⟨ab, hab, h7⟩
  exact h d hd5 hsq (by
    rw [← ZInQ.RouteK.Rank5b.det_M5b_eq_T5b hd5 hsq]
    exact ZInQ.RouteK.Rank5b.det_M5b_eq_one hd5 hsq h8 hab h7)
```


## 1. Faithfulness of the three statements

Fully elaborated statements (`#print` with `pp.fullNames`, scratch/rv-cr3-rank/stmts.txt):

```
def ZInQ.RouteK.Rank.CertifiedRankRk : Prop :=
∀ (d : ℕ),
  d % 8 = 5 →
    Squarefree d →
      (ZInQ.RouteK.Selmer.Sel2 d).ncard = 8 →
        (∃ ab ∈ ZInQ.RouteK.Selmer.Sel2 d, ab.1.natAbs % 8 = 7) →
          ∃ (P : (ZInQ.shortCurve (-↑d ^ 2)).toAffine.Point), ¬IsOfFinAddOrder P
def ZInQ.RouteK.Rank.CertifiedRankTYZRk : Prop :=
∀ (d : ℕ),
  d % 8 = 5 →
    Squarefree d → ZInQ.RouteK.Rank5b.T5b d = 1 → ∃ (P : (ZInQ.shortCurve (-↑d ^ 2)).toAffine.Point), ¬IsOfFinAddOrder P
def ZInQ.RouteK.Rank.CertifiedRankTYZClRk : Prop :=
∀ (d : ℕ),
  d % 8 = 5 →
    Squarefree d →
      ZInQ.RouteK.Rank5b.T5bCl d = 1 → ∃ (P : (ZInQ.shortCurve (-↑d ^ 2)).toAffine.Point), ¬IsOfFinAddOrder P
```

(`↑d : ℚ`; `-↑d ^ 2` is `−((d:ℚ)²)`.)

Checked:

- **Curve.** `ZInQ.shortCurve A` (`Model/Field/ShortWeierstrass.lean:22`) has `a₁ = a₂ = a₃ = a₆ = 0`,
  `a₄ = A`, so `shortCurve (−(d : ℚ)^2)` is `y² = x³ − d²x` over `ℚ` (the parse is `−((d:ℚ)^2)`).
  The point type is Mathlib's `WeierstrassCurve.Affine.Point` with Mathlib's group law
  (`#synth AddCommGroup` returns Mathlib's `Point.instAddCommGroup`), so `¬IsOfFinAddOrder P` is
  "`P` has infinite order in `C_d(ℚ)`". Equivalent to `rank C_d(ℚ) ≥ 1`, since `C_d(ℚ)` is
  finitely generated (`fg_points`).
- **Names.** `Sel2`, `Loc`, `T5b` and `shortCurve` each have a single definition in `ZInQKernel/`
  (grep). There are two `kummer`s, `ZInQ.Descent.kummer` (Kummer map of the 2-isogeny, used by
  RankMW) and `ZInQ.RouteK.Selmer.kummer` (complete 2-descent, used by `loc_iff_kummer`); RK9 uses
  the latter through `delta_eq_sqc_kummer`, so there is no mix-up. And the printed statements show `ZInQ.RouteK.Selmer.Sel2`,
  `ZInQ.RouteK.Rank5b.T5b`, `ZInQ.RouteK.Rank5b.T5bCl`. `Sel2 d` is the textbook 2-Selmer group of
  the complete 2-descent: squarefree integer pairs `(a, b)` (unique representatives of
  `(ℚ*/ℚ*²)²`) whose covering `Loc` is soluble over `ℝ` and every `ℚ_p`; `Loc K` is equivalent to
  "(a, b) is a Kummer image over K" for every field of characteristic ≠ 2 (`loc_iff_kummer`).
- **`CertifiedRankRk`** has exactly the premises of `Selmer.CertifiedRankSel`
  (`d % 8 = 5`, `Squarefree d`, `(Sel2 d).ncard = 8`, `∃ ab ∈ Sel2 d, ab.1.natAbs % 8 = 7`) and
  conclusion "point of infinite order". Under these premises it is *equivalent* to CR₃^Sel's
  conclusion (RK9 in one direction; in the other, 8 Selmer classes coming from points give
  `#C_d(ℚ)/2C_d(ℚ) ≥ 8 > 4 = #C_d(ℚ)[2]`, hence rank ≥ 1). Literature:
  - Kriz 10.13 + corank lemma: `dim Sel₂ = 3`, `dim C_d(ℚ)[2] = 2` give `corank Sel_{2^∞} +
    dim (Ш/Ш_div)[2] = 1`; Cassels–Tate makes the second term even, so the corank is 1, and Kriz
    gives rank 1. The `f₀ ≥ 4` condition and the unrefereed status of Kriz were reviewed in
    `pc-audit.md` RK1 and `rv-route-k.md` §3; nothing new here.
  - TYZ route: from the premises, Corollary 4.4 (`Rank5b.det_M5b_eq_one`, proved) and Theorem 3.6
    (`det_M5b_eq_T5b`, proved) give `T5b d = 1`; Rédei's formula turns this into TYZ's class-number
    sum; Proposition N gives `ord_{s=1} L = 1`; Gross–Zagier gives rank ≥ 1. I checked in Lean that
    `CertifiedRankTYZRk → CertifiedRankRk` (scratch example, §1.1). The docstring's TYZ bullet
    does not mention the Rédei and Corollary 4.4 steps (remark R1).
- **`CertifiedRankTYZRk`**: premises `d % 8 = 5`, `Squarefree d`, `T5b d = 1`; no
  `(Sel2 d).ncard = 8`. This is supported: Proposition N (`nt-tyz.md` line 51) has only the
  hypotheses "`n ≡ 5 (mod 8)` positive squarefree, `T_5b(n)` odd" (class-number form), and
  `RedeiFormula` covers exactly the blocks read by `T5b` (`T5bCl_eq_T5b`, proved). Gross–Zagier
  (RK7) needs no Selmer hypothesis either. Dropping `#Sel₂ = 8` is therefore *correct*, not an
  overreach: the derived `CertifiedRankTYZ` still has `#Sel₂ = 8` because RK9 needs it, and
  `certifiedRankTYZ_of_certifiedRankTYZRk` passes `h8` to RK9 only.
- **`CertifiedRankTYZClRk`**: premises `d % 8 = 5`, `Squarefree d`, `T5bCl d = 1`; this is literally
  Proposition N (with TYZ's own `g(d) = #2Cl(ℚ(√−d))`) followed by Gross–Zagier. Rédei is not part
  of the statement; the main theorem variant needs `RedeiFormula` because the chain to
  `FrozenTarget` goes through `CertifiedRankTYZ` (`certifiedRankTYZ_iff_of_redeiFormula`). The
  docstrings say so correctly.

No premise is stronger than the citations need, and none is weaker than they support.

### 1.1 Logical order of the three forms

`CertifiedRankTYZClRk ∧ RedeiFormula → CertifiedRankTYZRk → CertifiedRankRk`, the second arrow by
the proved Corollary 4.4 and Theorem 3.6 (checked by elaborating the five-line proof in a scratch
file; not in the repository). So `CertifiedRankRk` is the *weakest* hypothesis of the three, and
`exists_bounded_..._of_sixContactMin_certifiedRankRk` is the strongest main-theorem variant. Its
trust statement can rely on TYZ + Rédei + Gross–Zagier alone, without Kriz. KERNEL_PLAN calls the
TYZRk variant "the narrowest" (remark R2).

## 2. Soundness of the derivations

`RouteK/Rank/` (cr3-kummer):

- `kummerAt b e` (O ↦ 1, (e,0) ↦ 3e²+b, (x,y) ↦ x−e) is the standard Kummer map at a 2-torsion point
  (Silverman X.1.4 with `e' − e`·`e'' − e` = `3e² + b` at the root); `kummerAt_add` makes it a
  homomorphism. `delta d = (kummerAt 0, kummerAt d)` and `delta_eq_sqc_kummer` identify it with
  `Selmer.kummer` read in square classes, which is the map `loc_iff_kummer` uses. So the image of
  `δ` in `Sel2` is the same object as in CR₃^Sel.
- `delta_eq_one_iff` (over ℚ, `δ P = 1 ↔ P ∈ 2C_d(ℚ)`): genuine two-sided statement; the halving
  formula `exists_two_nsmul_eq_of_squares` covers the generic case and the torsion cases are
  excluded because `−d²` (for `(0,0)`), `2d²` (for `(d,0)`) and `−d` (for `(−d,0)`, whose first
  coordinate would have to be a square) are not rational squares. `deltaHom_ker_eq` restates it as
  `ker δ = (nsmulAddMonoidHom 2).range`.
- `selRep` / `repPair` pick squarefree representatives (`sqfRep`, injective), so
  `#(C_d(ℚ)/2C_d(ℚ)) = #range selRep` (`card_quotient_two_eq_ncard_range_selRep`) is an honest
  bijection count (first isomorphism theorem plus an injective relabelling). `selRep_mem_sel2`
  transports `Loc ℚ` to `ℝ` and `ℚ_p` along the ring maps (`loc_map`).
- `card_ker_two_nsmul_eq_four` (any field, `2 ≠ 0`, `d ≠ 0`): `C_d[2] = {O,(0,0),(d,0),(−d,0)}`.
- `eight_le_card_quotient_two`: structure theorem `A ≃ ℤⁿ × T`, `n ≥ 1` from the element of infinite
  order. It assumes `[Finite (A/2A)]` to avoid `Nat.card = 0`; in `loc_of_mem_sel2_of_infinite_order`
  that instance is derived from `Sel2 d` being finite (`ncard = 8 ≠ 0`) and `range selRep ⊆ Sel2 d`,
  not assumed. No `Nat.card`/`ncard` of an infinite set is silently 0 anywhere in the chain:
  `hfin` comes from `ncard = 8`, and `hSpos` from `0 ∈ C_d(ℚ)`.
- `loc_of_mem_sel2_of_infinite_order` (RK9): hypotheses `d ≠ 0`, `AddGroup.FG`, a point of infinite
  order, `(Sel2 d).ncard = 8`. None is contradictory: they hold together exactly when
  `rank C_d(ℚ) = 1` and `Ш(C_d)[2] = 0` (by RK9 itself and the converse in §1), which the
  literature gives for the `d` CR₃ is applied to. Conclusion is `∀ ab ∈ Sel2 d, Loc ℚ d a b`
  for the same `Selmer.Sel2`.

`RouteK/RankMW/` (cr3-mw):

- `mwPhi_add` / `mwPhiHom`: additivity of the 2-isogeny `phi` of `Model/Descent/Kummer.lean`, for
  all points including the degenerate ones (`P = ±Q`, `(0,0)`, vertical lines), as a bundled
  `AddMonoidHom`; no extra hypotheses beyond `b ≠ 0`-type data.
- `mwFiniteIndex_two_of_kummer`: `[E : 2E]` finite from finiteness of the two Kummer images, via
  `ker α_b = φ̂(E')` and `ker α_{b'} ≤ φ̂⁻¹(2E)` (standard Silverman X.4.7-style argument).
- `mwKummer_range_finite (c : ℤ)`: image of `kummer c` over ℚ lies in classes of signed divisors of
  `c` (valuation argument); hypotheses only `c ≠ 0`.
- `fg_points d hd`: `AddCommGroup.fg_of_descent'` with Mathlib's naive height, its nonnegativity,
  `approx_parallelogram_law` and Northcott; the only hypothesis is `d ≠ 0`. It is unconditional
  Mordell–Weil for every `C_d`, `d ≠ 0`, and `RankVariants.fg_points_all` discharges `hfg`.

`RouteK/RankVariants.lean`: the three main-theorem variants compose the above with the existing
`..._certifiedRankSel`, `..._certifiedRankTYZ`, `..._certifiedRankTYZCl`; no new hypotheses.

Forbidden constructs: none (`axiom`, `native_decide`, `implemented_by`, `extern`, `sorry`, `admit`,
`unsafe`, `opaque`, `set_option` all absent from the reviewed files).

## 3. Axioms and build

See "Build and axioms" at the top: build passes, all 38 entries show only the three standard axioms.

## 4. Docstrings and KERNEL_PLAN.md

Accurate overall: the trust statements say what is proved in Lean (RK9, Mordell–Weil, Corollary 4.4,
Theorem 3.6, Rédei's formula as a Prop) and what is cited (Kriz, TYZ/Proposition N, Gross–Zagier).
The module docstring of `Rank/RK9.lean` describes the proof faithfully. Remarks R1–R4 below.

## 5. Non-blocking remarks

- **R1** (`RouteK/Rank/Statements.lean:30–34`, TYZ bullet of `CertifiedRankRk`). From the premises
  `#Sel₂ = 8`, `|a| ≡ 7` to TYZ's hypothesis one needs Corollary 4.4 and Theorem 3.6 (proved in Lean)
  *and Rédei's formula* (a Prop, not proved), since Proposition N is stated with TYZ's class numbers
  `g(d)`. The bullet cites only TYZ and Gross–Zagier. Same omission in the inherited
  `Selmer.CertifiedRankSel` docstring (`Selmer/Covering.lean:370–374`). Suggest: "Tian–Yuan–Zhang …
  through Corollary 4.4, Theorem 3.6 (`det_M5b_eq_one`, `det_M5b_eq_T5b`, proved) and Rédei's formula
  (`Rank5b.RedeiFormula`)".
- **R2** (`KERNEL_PLAN.md:152–154`). "The narrowest is `…_certifiedRankTYZRk`" is inaccurate if
  "narrowest" means weakest hypothesis: `CertifiedRankTYZRk → CertifiedRankRk` holds in Lean (§1.1),
  so `CertifiedRankRk` is weaker. What is true is that TYZRk is the form whose content is *literally*
  "TYZ (Proposition N) + Rédei + Gross–Zagier" with no Selmer hypothesis. Suggest rewording, and
  adding `certifiedRankRk_of_certifiedRankTYZRk` (five lines, proof in §1.1) to `Statements.lean`.
- **R3** (`Statements.lean:7–14`, module docstring). "forms whose conclusion is exactly what the
  published theorems give": Kriz gives more (rank exactly 1 and `Ш` finite); "at most what" would be
  precise. Cosmetic.
- **R4** (`Selmer/Covering.lean:368–369`, inherited, not new). "Poonen–Stoll: the Cassels–Tate pairing
  makes `dim Ш[2]` even when `Ш` is finite": the corank lemma needs the version for `Ш/Ш_div`
  (Cassels–Tate is nondegenerate there without finiteness of `Ш`), since finiteness of `Ш` is not
  known a priori. The conclusion is unaffected.
