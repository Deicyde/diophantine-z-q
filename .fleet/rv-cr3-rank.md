# rv-cr3-rank report: adversarial review of CR₃ in positive-rank form

Full review: docs/research/rv-cr3-rank.md. Evidence: scratch/rv-cr3-rank/{axioms.txt, stmts.txt,
build-tail.txt, log.md}. No Lean files were edited.

## Verdict: no blocker

1. **Faithfulness.** `CertifiedRankRk`, `CertifiedRankTYZRk` and `CertifiedRankTYZClRk`
   (RouteK/Rank/Statements.lean) elaborate to "∃ P : (ZInQ.shortCurve (−(d:ℚ)²)).toAffine.Point,
   ¬IsOfFinAddOrder P". The curve is y² = x³ − d²x, the group is Mathlib's `Point.instAddCommGroup`,
   and the names resolve to `Selmer.Sel2`, `Rank5b.T5b` and `Rank5b.T5bCl`. Premises:
   - The Rk form has exactly CR₃^Sel's premises. Under them it is equivalent to CR₃^Sel's conclusion.
   - The TYZ forms drop `#Sel₂ = 8`. This is justified: Proposition N (nt-tyz.md) assumes only
     squarefree n ≡ 5 (mod 8) and an odd genus sum, and Gross–Zagier adds no Selmer hypothesis.
   - The derived `CertifiedRankTYZ(Cl)` keep `#Sel₂ = 8` for RK9.
2. **Soundness.** RK9 (`loc_of_mem_sel2_of_infinite_order`) is a genuine counting argument:
   - ker δ = 2C_d(ℚ), δ lands in `Selmer.Sel2`, #C_d[2] = 4, and the structure theorem gives
     #(A/2A) ≥ 8.
   - The finiteness of A/2A is derived from `ncard = 8`, not assumed. No `Nat.card` of an infinite
     type is silently 0.
   - `fg_points` is unconditional Mordell–Weil for every C_d with d ≠ 0. It uses the additive
     2-isogeny, the finite index and Mathlib's descent and height theorems.
   - No hypothesis is vacuous. There is no `axiom`, `sorry`, `native_decide` or `set_option` in the
     reviewed files.
3. **Build and axioms.** `lake build ZInQKernel` succeeds (9906 jobs). `lake env lean
   scripts/print_axioms.lean` prints 38 entries, and each shows only `[propext, Classical.choice,
   Quot.sound]`.
4. **Docstrings and KERNEL_PLAN.** They are accurate apart from the non-blocking remarks below.

## Non-blocking remarks (details in docs/research/rv-cr3-rank.md §5)
- **R1, Statements.lean:30–34.** The TYZ bullet of `CertifiedRankRk` omits two steps needed to reach
  TYZ's hypothesis from `#Sel₂ = 8, |a| ≡ 7`:
  - Corollary 4.4 and Theorem 3.6 (`det_M5b_eq_one`, `det_M5b_eq_T5b`), which are proved;
  - Rédei's formula, which is a Prop.

  The inherited `Selmer.CertifiedRankSel` docstring has the same omission.
- **R2, KERNEL_PLAN.md:152–154.** It calls the TYZRk variant "the narrowest". In fact
  `CertifiedRankTYZRk → CertifiedRankRk`: a five-line proof from `det_M5b_eq_one` and
  `det_M5b_eq_T5b` elaborated in a scratch file, and the code is in the review. So `CertifiedRankRk`
  is the weakest hypothesis. Suggestions:
  - add `certifiedRankRk_of_certifiedRankTYZRk` to Statements.lean;
  - reword KERNEL_PLAN to say that TYZRk is the form whose content is literally TYZ, Rédei and
    Gross–Zagier.
- **R3, module docstring of Statements.lean.** It says "exactly what the published theorems give".
  Kriz gives more than that (rank exactly 1 and Ш finite). This is cosmetic.
- **R4, Covering.lean:368–369, inherited.** The corank lemma should cite Cassels–Tate on Ш/Ш_div,
  not "dim Ш[2] even when Ш is finite".

## Not done
- No numerical spot check of the cited theorems: earlier audits cover this (pc-audit RK6, 900 curves;
  nt-tyz).
- I did not re-review the literature behind Kriz 10.13 or Proposition N. That review is in
  pc-audit.md, rv-route-k.md and rv-nt-tyz.md.
