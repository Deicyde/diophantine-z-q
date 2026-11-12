# pkg-I5 (Arakelov package: E2-E4, F3) — fleet report

**Main result.** I5 needs the stable Faltings height of abelian varieties of dimension up to `N²`.
E2-E4 go through `J₁(N)` and the complement `Z`, and every published theorem there (Javanpeykar,
Gaudron–Rémond Thm 1.4, Faltings Lemma 5, Bost) is an inequality in `h_F` of those varieties. No
explicit formula reaches them: `X₁(N)` is hyperelliptic for only three `N`. No elementary height
can replace `h_F` either: that would take a published comparison in dimension `N²`, or an
effective Shafarevich theorem, which is open. So a faithful I5 needs a new **object layer**:
abelian varieties over number fields, isogeny degree, stable `h_F`, Jacobians, `X₁(N)`, Belyi
degree and theta height. Nothing in Mathlib, Tau Ceti or the FLT projects provides it. For the
QM surface `A` alone, much becomes concrete:

- Thomae's formula turns the theta height of a genus-2 Jacobian into an elementary height of
  root-difference polynomials. Their sum is the Igusa–Clebsch `I₄` and their product is `disc⁴`.
- The archimedean term of `h_F` is a Lebesgue integral over `ℂ`.
- For elliptic curves, and for genus-2 curves with a smooth model over `𝓞_K`, `h_F` has a closed
  formula.

`h_F(A)` cannot be traded for an elementary height inside a leaf; it can only be composed away
(E∘F3), and that composite is not a published theorem.

**Leaves / glue.**

- Leaves, stated over the object layer (Lean-shaped templates in `docs/research/pkg-I5.md` §3):
  Javanpeykar 1.1.1, GR14 Thm 1.4, Faltings Lemma 5 (inequality form), Bost
  `h_F ≥ −(3/2)dim`, Pazuki Cor. 1.3(2) at `g = r = 2`.
- Glue:
  - G1: `X₁(N)` has genus and Belyi degree `≤ N²`; base change.
  - G2: E3-E4 numerics, proved (wk-h `transfer_numerics`).
  - G3: F3 numerics, proved here (`f3_numerics`).
  - G4: dimension bookkeeping and additivity.
  - G5: field and model independence, partly proved.
- Proposal: build the object layer as a crowdsourced sub-project with acceptance tests. The
  general `h_F` must equal `faltingsHeightEC` and `faltingsHeightGood`, which compile today and
  were checked numerically.

**What compiles.** `scratch/pkg-I5/I5.lean` (Mathlib-only, no `sorry`, standard axioms):

- definitions `thomaePoint`, `thetaHeightThomae`, `hypGram`/`hypVol`, `faltingsHeightEC`,
  `Genus2Eq.Good`, `faltingsHeightGood`;
- leaves statable now: `BostEC`, `BostGoodGenus2`, `PazukiGoodGenus2` (faithful special cases;
  the last is a composite through Thomae);
- proved: `f3_numerics`, `thomaePoint_add_const`, `thomaePoint_smul`.

Numerical checks (PARI/mpmath/sympy):

- the `h_F` formula for elliptic curves matches Silverman/BCCGM (6.2) on 7 curves;
- `j = 0` gives Deligne's minimum shifted by `−½ log π`;
- 11a1 → 11a3 attains Faltings' `½ log 5`;
- the area integral matches the PARI period lattice;
- the Thomae identities hold on 27 random root sets.

**Biggest obstacle.** There is no Lean definition of the stable Faltings height: it needs Néron
models (or the infimum over smooth group models, §2.1) and integration over `A_σ(ℂ)`. The next
biggest gap is `J₁(N)` as an abelian variety over `ℚ`, with Belyi degrees. The good-model genus-2
leaves do not cover every QM surface: its curve can have compact-type bad reduction.
