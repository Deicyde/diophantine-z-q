# pkg-I5 log

Task pkg-I5: package I5 (Arakelov: E2-E4, F3). Marks: VERIFIED (read in a source, computed, or
compiled), STANDARD (published, exact reference), SPECULATIVE. Locators recalled from memory are
UNVERIFIED (no network).

## Step 1. Sources read (VERIFIED by reading)

- N5 L377-410 (constants), L581-631 (CM branch), L858-964 (transfer and return to `u`),
  bibliography L11060-11100.
- h-trust §1 E1-E4, F1-F4, §2.5 (ASTRA-READ table); wk-h §§1-6 and `scratch/wk-h/Arakelov.lean`
  (signature, `transfer_numerics` proved); rv-lit §5-7; prereq-survey (no Faltings height in any
  library); h-cm (CM branch empty for rational `u`, so B_cm, C_cm, BCCGM (6.2), Fowler drop out).
- `docs/reviews/height-replacement/height/AUDIT.md` item 3 (Javanpeykar Thm 1.1.1:
  `h_F(Jac X) ≤ 13·10⁶ g deg_B(X)⁵`, §2.1 metric `(i/2)∫ω∧ω̄`, §2.3 = stable height of Jacobian,
  pp. 92-93 Belyi degree ≤ index), item 4 (GR14 `κ(A)`, Thm 1.4 both directions, no
  principal-polarization hypothesis, §9 Bost `h_F ≥ −3 dim/2`). These are ASTRA-READ.

## Step 2. Mathlib v4.35 inventory for I5 (VERIFIED by grep)

- present: `ModularForm.discriminant` (Δ = η²⁴), `ModularForm.eta`, `Petersson.lean`,
  `WeierstrassCurve` with `j`, `Δ`, minimal models over a DVR (`EllipticCurve/Reduction.lean`:
  `IsMinimal`, `exists_isMinimal`, `HasGoodReduction`), `Polynomial.discr`, `Height.logHeight`,
  `Height.logHeight_pow` (`h(x^n) = n h(x)`), `Height.logHeight₁`, number-field
  `AdmissibleAbsValues` instance, group schemes over a field (`AlgebraicGeometry/Group/*`),
  smooth/proper/finite/flat morphisms, Lebesgue measure on `ℂ`.
- absent: abelian varieties over number fields beyond group-scheme generalities, Néron models,
  Picard schemes/Jacobians, analytification of schemes, modular curves as schemes, Belyi maps,
  isogeny degree, Faltings height, Siegel modular forms, theta constants in genus ≥ 2,
  hyperelliptic curves.

## Step 3. Numerical checks (VERIFIED by computation)

- `ec_height_check.py` (PARI): the closed formula `faltingsHeightEC` (integral form) agrees with
  Silverman Prop. 1.1 / BCCGM (6.2) (τ form) on 7 curves to 6 decimals; `j = 0` gives
  −1.321117 = −0.748752 − ½ log π (Deligne's minimum in Faltings' normalization); 11a1 −0.308010,
  11a3 −1.112729, difference 0.804719 = ½ log 5 (Faltings Lemma 5 attained by the 5-isogeny).
- `area_check.py` (mpmath + PARI): `2∫_ℂ dλ/|f|` equals the covolume of the period lattice of
  `dx/y` for 3 cubics (6.87519, 4.95638, 16.2173; first run had a wrong scale for PARI's
  `dx/(2y)` in the script, corrected; rerun output in `area_check.output.txt`).
- `thomae_check.py` (sympy): `∏_T Θ_T = disc⁴` (monic) and translation/scaling behaviour on 27
  random root sets; `∑_T Θ_T` is symmetric (it is the Igusa–Clebsch `I₄` sum over splittings).

## Step 4. `I5.lean` (VERIFIED: compiles with `lake env lean`, no errors, no sorry)

- definitions: `thomaePoint`, `absLogHeight`, `thetaHeightThomae`, `hypGram`, `hypVol`,
  `finiteHeightPart`, `faltingsHeightEC`, `Genus2Eq` (`P`, `binDisc`, `Good`),
  `faltingsHeightGood`, `pazukiC2`.
- leaves (`def … : Prop`): `BostEC`, `BostGoodGenus2`, `PazukiGoodGenus2` (composite).
- proved: `thomaePoint_add_const`, `tripleProd_mul`, `card_evenTriple`, `thomaePoint_smul`,
  `f3_numerics` (Pazuki output ⇒ `h([z_m]) ≤ 10000·2²⁴ max(1, h_F)`); axioms of the three
  printed: `propext, Classical.choice, Quot.sound`.

## Step 5. Report `docs/research/pkg-I5.md` written

- Main finding: `h_F` of abelian varieties of dimension up to `N²` (`J₁(N)`, `Z`) is needed by
  every E2-E4 leaf; no explicit formula or elementary replacement exists (argument in §2.2);
  genus-1 and good-model genus-2 formulas and the Thomae theta height are concrete (§§2.3-2.5).
- Direction analysis (§2.6): `h_F(A)` can be eliminated only by composing E with F3.
- Recommendation: five leaves over an object layer with acceptance tests (§5).
