# cr3-kummer report

## Result
RK9 (docs/research/pc-audit.md) is proved in Lean. With Mordell–Weil for C_d(ℚ) as the explicit hypothesis
`hfg : ∀ d : ℕ, d ≠ 0 → AddGroup.FG (shortCurve (-(d : ℚ) ^ 2)).toAffine.Point`, the CR₃ hypotheses
CR₃^Sel, CR₃^TYZ and CR₃^TYZ_Cl follow from forms whose conclusion is "C_d(ℚ) has a point of infinite order".
There is no sorry, and the only axioms are propext, Classical.choice and Quot.sound (checked with #print axioms on all
five main theorems). `lake build ZInQKernel` succeeds.

## Files (namespace ZInQ.RouteK.Rank, root module ZInQKernel/RouteK/Rank.lean, imported from ZInQKernel.lean)
- `Rank/KummerAt.lean`: `kummerAt b e`, the Kummer map at a root e of x³+bx on y²=x³+bx
  (O ↦ 1, (e,0) ↦ 3e²+b, (x,y) ↦ x−e). `kummerAt_add` proves it is a homomorphism, following Descent.kummer_add.
  The chord identity is `mul_addX_sub_eq`. Also `tRootPt` (the point (e,0)) and `kummerAtHom`.
- `Rank/Delta.lean`: `delta d P = (kummerAt (-d²) 0 P, kummerAt (-d²) d P)`, the complete 2-descent map over any field
  with 2 ≠ 0 and d ≠ 0. `delta_add` and `deltaHom` make it a homomorphism. `delta_eq_sqc_kummer` shows it is
  `Selmer.kummer` read in square classes, so it has the requested values at the torsion points.
  `delta_two_nsmul` shows it kills 2C_d. The halving lemma is `exists_two_nsmul_eq_of_squares`:
  if x=r₁², x−d=r₂², x+d=r₃², then (x,y) = 2Q, using the explicit formula
  Q = (x+r₁r₂+r₁r₃+r₂r₃, (r₁+r₂)(r₁+r₃)(r₂+r₃)) and the fact that points with equal x are equal or opposite.
- `Rank/Image.lean`:
  - `sqfRep`: the squarefree integer representative of a class in ℚ*/ℚ*².
  - `loc_map`, `loc_cast_of_loc_rat`: Loc transported along ℚ → ℝ and ℚ → ℚ_p.
  - `delta_eq_one_iff`: over ℚ, δ(P)=1 ↔ P ∈ 2C_d(ℚ). The torsion points are excluded because −d², 2 and −d are
    not rational squares.
  - `selRep P` (representatives of δ(P)), `loc_selRep` (via Selmer.loc_iff_kummer), `selRep_mem_sel2`.
- `Rank/Counting.lean`:
  - `card_quotient_two_eq_card_ker`: #T/2T = #T[2] for a finite T.
  - `eight_le_card_quotient_two`: if A is f.g. with #A[2] = 4, has an element of infinite order, and A/2A is finite,
    then #(A/2A) ≥ 8. Proof: structure theorem A ≅ ℤⁿ × T, n ≥ 1, and a surjection A → ℤ/2 × T/2T that kills 2A.
  - The finiteness assumption on A/2A comes for free in the application, since A/2A embeds in Sel2.
- `Rank/Torsion2.lean`: `ker_two_nsmul_eq` (C_d(K)[2] = {O,(0,0),(d,0),(−d,0)}) and `card_ker_two_nsmul_eq_four`.
- `Rank/RK9.lean`:
  - `deltaHom_ker_eq` and `card_quotient_two_eq_ncard_range_selRep`: #(C_d(ℚ)/2C_d(ℚ)) = #image.
  - **`loc_of_mem_sel2_of_infinite_order`** (RK9): under hfg, a point of infinite order and (Sel2 d).ncard = 8,
    every ab ∈ Sel2 d satisfies Loc ℚ d ab.1 ab.2.
- `Rank/Statements.lean`: the definitions `CertifiedRankRk`, `CertifiedRankTYZRk` and `CertifiedRankTYZClRk`,
  stated exactly as in the task with trust-statement docstrings. Theorems:
  - `certifiedRankSel_of_certifiedRankRk`
  - `certifiedRankTYZ_of_certifiedRankTYZRk`
  - `certifiedRankTYZCl_of_certifiedRankTYZClRk`
  - `certifiedRank_of_certifiedRankRk`, an extra theorem that composes with Selmer.certifiedRank_of_certifiedRankSel.

All of these take `hfg`.

## Statement notes
- All names and types were checked against the repository (shortCurve, Sel2, Loc, T5b, T5bCl, IsOfFinAddOrder).
  The statements were kept unchanged.
- CertifiedRankTYZRk and CertifiedRankTYZClRk drop the premise `(Sel2 d).ncard = 8`, as the task specified.
  The derived theorems still have that premise, because it is a hypothesis of CertifiedRankTYZ(Cl).
- 2C_d(ℚ) is expressed as `(nsmulAddMonoidHom 2).range` and C_d(ℚ)[2] as `(nsmulAddMonoidHom 2).ker`.

## Left / suggestions
- When cr3-mw is merged, discharge `hfg` with its Mordell–Weil theorem for C_d over ℚ. This only means replacing the
  hypothesis in the four theorems of Statements.lean; the right form is `∀ d ≠ 0, AddGroup.FG ...`.
- scripts/print_axioms.lean was not edited, since the task named no lines there.
  Suggested lines: the five theorems above, plus `loc_of_mem_sel2_of_infinite_order`.
- The main-theorem variants (exists_bounded_..._of_sixContactMin_certifiedRankRk etc.) can be added by the lead
  through certifiedRank_of_certifiedRankRk.

## Method note
The linear_combination coefficients for the chord identity and the halving formula were computed with sympy, by
pseudo-division modulo the curve equations and the slope relation. Every proof compiled on the first or second try.
