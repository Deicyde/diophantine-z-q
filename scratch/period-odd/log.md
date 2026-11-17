# period-odd results log

Task: prove `ZInQ.CdOpt.CdTwistedPeriodOdd` (ZInQKernel/Contrib/OneProof/CdOptimal.lean), or reduce it;
target: hL3 replaced by `GrossZagierModuliOptCd` + `EtaW32Character` only.

## 2026-11-16

- Build: copied `.lake/build` and `lean/.lake/build` from the cd-optimal worktree (same commit 04d7251c).
  Probe import of `ZInQKernel.Contrib.OneProof.CdOptimal` compiles (1.5 min). VERIFIED.
- Plan (bypass of CdTwistedPeriodOdd): GZHL3.GrossZagierFormulaCd from GrossZagierModuliOptCd + EtaW32Character,
  by a case split on `Λ_d ⊄ (1+i)L`:
  * yes: cd-optimal's route A (lattice_eq_of_periods + core_selfOptimal);
  * no: `Λ_d = k(1+i)L`, so `L' = ((1+i)/2)L = Λ_d/(2k)` is the period lattice of the 2-isogenous
    `E' : y² = x³ + 4d²x`, `E'` is optimal; apply the GZ leaf at `E'` (it covers every short model in the class)
    and transfer to `C_d` along the explicit 2-isogeny `(x,y) ↦ (y²/x², y(x²+d²)/x²)` (analytic form: z ↦ z,
    ℂ/L → ℂ/L').
  Needs in Lean: (A) `E'.LFunction = C_d.LFunction`; (C) the analytic isogeny identity; (D) the bad-case lattice.
- Numerical check (scratch/period-odd/isog_check.gp, d = 5, PARI): with L = ℤ[i]ω the lattice of C_d,
  h = (1+i)ω/2, L' = ((1+i)/2)L: ℘_L(h) = 0; ℘_{L'}(z) = x − d²/x; ℘'_{L'}(z)/2 = y(x²+d²)/x²;
  ℘_L(z+h) = −d²/x; ℘'_L(z+h)/2 = d²y/x²; (℘_{L'}, ℘'_{L'}/2) on y² = x³ + 4d²x. All residuals < 1e-12. VERIFIED.
- Character-sum identity used for (A) (derivation, to be compiled): for a ≠ 0, char ≠ 2,
  Σ_x χ(x³+ax) = Σ_{x≠0} χ(x + a/x) = Σ_X χ(X)(1 + χ(X²−4a)) = Σ_X χ(X³ − 4aX).
- (A) DONE: `ZInQKernel/Contrib/OneProof/PeriodOdd/LFunction.lean` compiles (`lake env lean`, 7 s);
  `ZInQ.PeriodOdd.LFunction_ePrime_eq (hd : Odd d) (hsq : Squarefree d) : (ePrime d).LFunction =
  (shortCurve (-(d : ℚ) ^ 2)).LFunction`, `ePrime d := shortCurve (4 * d^2)`; axioms
  [propext, Classical.choice, Quot.sound]. VERIFIED. Ingredients: `charSum_isog` (Σχ(x³+ax) = Σχ(X³−4aX), a ≠ 0),
  minimality of y² = x³+4d²x at 2 from c₄ (v₂(c₄) = 6), additive at p | 2d, good at p ∤ 2d.
- (C) DONE: `ZInQKernel/Contrib/OneProof/PeriodOdd/Isogeny.lean` builds (`lake build`, 7 s).
  `weierPt_ePrime_eq (hd : d ≠ 0) (hL : IsPeriodLattice C_d L) (z) : isogPt hd (weierPt C_d L z) =
  weierPt (ePrime d) (latP L) z` with `latP L = scalePP L ((1+i)/2)`, `isogPt (x,y) = (x − d²/x, y(x²+d²)/x²)`,
  `(0,0), O ↦ O`; `map_isogPt` (commutes with ℚ-algebra maps); `isPeriodLattice_ePrime`;
  `weierstrassP_split`/`derivWeierstrassP_split` (℘ over L' = L ⊔ (h+L)); `weierstrassP_I_mul` (℘(iz) = −℘(z)).
  Axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
- (D)+(E) DONE: `ZInQKernel/Contrib/OneProof/PeriodOdd.lean` builds (`lake build ZInQKernel.Contrib.OneProof.PeriodOdd`).
  `ZInQ.PeriodOdd.grossZagierFormulaCd_of_etaW32 : GrossZagierModuliOptCd → EtaW32Character → LamCdNeZero →
  GZHL3.GrossZagierFormulaCd`, axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
  * `lattice_cases`: Λ_d ⊆ L, Λ_d ≠ 0 ⇒ L = c₀Λ_d (c₀ ∈ ℚ) or L' = ((1+i)/2)L = cΛ_d (c ∈ ℚ).
  * `core_isog`: GZ leaf at E'_d + φ ⇒ formula at C_d.
  New residual: `LamCdNeZero` (∃ nonzero period of Φ_d for Γ₀(32d²)); CdTwistedPeriodOdd is no longer needed.
  Finding: the bypass needs Λ_d ≠ 0, which CdTwistedPeriodOdd implied; the tree has no proof of it (searched
  ZInQKernel/Contrib for periodLattice/LamCd nonvanishing: none).
- `LamCdNeZero` PROVED (so dropped): `ZInQKernel/Contrib/OneProof/PeriodOdd/NeZero.lean`,
  `ZInQ.PeriodOdd.periodLattice_ne_zero (f : Newform N 2) : ∃ l ∈ periodLattice f, l ≠ 0` (any level, any
  character): a Γ₀(N)-invariant Eichler integral is a weight-0 modular form (holomorphic: gz-heegner `mdiff_eichler`;
  bounded at every cusp: gz-heegner `exists_const_eichler` + `analyticAt_Gser`), constant by Mathlib's
  `ModularForm.eq_const_of_weight_zero`, so f = D φ_f = 0. Axioms standard. VERIFIED.
- TARGET MET: `ZInQ.PeriodOdd.grossZagierFormulaCd_of_etaW32 : GrossZagierModuliOptCd → EtaW32Character →
  GZHL3.GrossZagierFormulaCd`, axioms [propext, Classical.choice, Quot.sound]. VERIFIED (lake build + #print axioms).
- Added `cd_or_ePrime_optimal` (from EtaW32Character: C_d or E'_d has period lattice ℚ^×·Λ_f). Axioms standard. VERIFIED.
- MainEdit.lean: `frozenTarget_periododd` (cd-optimal's frozenTarget_cdoptimal minus `CdTwistedPeriodOdd`),
  axioms standard (out_mainedit.txt). VERIFIED.
- #discharges: 61 open, 3247 theorems, 9 discharge one (same 9 lines as cd-optimal; none by period-odd: the field
  grossZagierFormulaCd exists only after the C_d split of hL3). VERIFIED (discharges-output.txt).
- autofold.json: field grossZagierFormulaCd, leaves grossZagierModuliOptCd + etaW32Character (published, flag "").
  `autofold.py --dry-run`: "not a field of the current bundles: ['grossZagierFormulaCd']" — same for cd-optimal's
  autofold-formula.json (VERIFIED). Expected until the C_d split is folded.
- CdTwistedPeriodOdd: NOT proved; no longer needed. Status/rating in report §4 (GLUE, not printed, SPECULATIVE route).
- Report: docs/research/period-odd.md.
