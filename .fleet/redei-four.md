# redei-four: step 6 of the Rédei plan and the assembly of `RedeiFormula`

## Result

`ZInQ.RouteK.Rank5b.RedeiFormula` is now a theorem: `ZInQ.RouteK.Redei.redeiFormula`
(`ZInQKernel/RouteK/Redei/FourRank.lean`). No `sorry`, no new axioms (axiom check below).

## The defect in `OddGClStatement` (fixed first)

`OddGClStatement` (`Redei/Bridge.lean`) quantified over all odd squarefree `n`, including `n = 1`,
where it is false (`ℚ(i)`: `gCl 1 = 1` is odd, but the nonzero vector supported at `2 ∈ ramSet 1`
solves the empty Rédei system and is not `e_1 = 0`). It now has the hypothesis `1 < n`. The new lemma
`redeiB_one_lt : B.Nonempty → 1 < dProd B` supplies it in `gCl_dProd_eq_gBit` (and so in
`redeiFormula_of_oddGClStatement`). The other Bridge statements already take `B.Nonempty` or are
about `dProd B`, so they had no such gap.

## `Redei/FourRank.lean` (new, added to `ZInQKernel/RouteK/Redei.lean`)

Group theory:
* `odd_card_range_sq_iff` (copied from the probe): `#G²` odd ↔ `G[2] ⊓ G² = ⊥`;
* `card_ker_sq_mul_card_range_sq`: `#G[2] · #G² = #G`;
* helpers `fourRank_sq_eq_one`, `fourRank_eq_of_mul_eq`, `fourRankSum` (the sum map
  `𝔽₂^ι → 𝔽₂`, multiplicative) and `card_ker_fourRankSum` (`#hyperplane · 2 = 2^#ι`).

Class groups, for odd squarefree `n` (with `1 < n` where needed):
* `chi_psi`: `χ_q(ψ(e)) = Σ_p R_{qp} e_p` (proof suggested by redei-genus, unchanged);
* `genusMap n : Cl →* Multiplicative (n.primeFactors → ZMod 2)`, `mem_ker_genusMap`,
  `range_sq_le_ker_genusMap` (squares are killed: the target has exponent 2);
* `pow_le_card_range_genusMap`: `2^{t−1} ≤ #χ(Cl)` from `exists_chi_eq` (all of `𝔽₂^r` if
  `n ≢ 3 (mod 4)`, `t = r + 1`; the sum-zero hyperplane if `n ≡ 3 (mod 4)`, `t = r`);
* `range_sq_eq_ker_genusMap_and_card`: from `#Cl² · #Cl[2] = #Cl = #ker χ · #χ(Cl)`,
  `Cl² ≤ ker χ` and `#Cl[2] ≤ 2^{t−1} ≤ #χ(Cl)` (`card_ker_sq_le`), equality throughout;
* `range_sq_eq_ker_chi` (probe statement plus `1 < n`): `Cl² = ⨅ q, ker (chi n q)`;
* `card_ker_sq_eq`: `#Cl[2] = 2^{t−1}`; `card_ker_psi`: `#ker ψ = 2`;
* `fourRankVec`, `fourRankVec_ne_zero`;
* `odd_gCl_iff` (probe statement plus `1 < n`): `g(n)` odd iff the kernel of the Rédei matrix
  is `{0, e_n}`.

Assembly:
* `oddGClStatement : OddGClStatement`;
* `redeiFormula : RouteK.Rank5b.RedeiFormula` (`redeiFormula_of_oddGClStatement oddGClStatement`);
* `T5bCl_eq_T5b'` (`T5bCl d = T5b d` for odd squarefree `d`), `certifiedRankTYZ_iff'`
  (`CertifiedRankTYZCl ↔ CertifiedRankTYZ`), `certifiedRankTYZRk_of_certifiedRankTYZClRk`
  (`CertifiedRankTYZClRk → CertifiedRankTYZRk`).

## Main-theorem variants (changed in place, no import cycle)

`RouteK/Rank5bSec3.lean` now imports `ZInQKernel.RouteK.Redei.FourRank`, and the argument
`hR : RouteK.Rank5b.RedeiFormula` is gone from
* `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZCl`
  (`RouteK/Rank5bSec3.lean`): from `SixContactMin` and `CertifiedRankTYZCl`;
* `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankTYZClRk`
  (`RouteK/RankVariants.lean`): from `SixContactMin` and `CertifiedRankTYZClRk`.
Docstrings updated; no `RedeiVariants.lean` was needed. The docstring of `RedeiFormula`
(`RedeiStatement.lean`) now points to `redeiFormula`. `scripts/print_axioms.lean` gains
`oddGClStatement`, `redeiFormula`, `certifiedRankTYZ_iff'`,
`certifiedRankTYZRk_of_certifiedRankTYZClRk` (the two changed main-theorem variants were already
listed).

## The proof chain of `RedeiFormula`

`redeiFormula = redeiFormula_of_oddGClStatement oddGClStatement` (step 8, Bridge), where
`oddGClStatement n hn hsq h1 = odd_gCl_iff n hn hsq h1` (step 6), built from
`range_psi`, `card_ker_sq_le`, `psi_ones` (step 3, Ambiguous), `chi_prod_ramIdeal` (step 4, Genus),
`exists_chi_eq` (step 5, Dirichlet: Dirichlet's theorem, CRT, Jacobi reciprocity) and the counting
above; step 8 then uses `redeiB_kernel_iff` and `kernel_trivial_iff_redeiG` (step 7, Kernel) to turn
the 4-rank statement for `n = d_B` into `gCl (dProd B) ≡ gBit d B (mod 2)`.

## Paragraph for KERNEL_PLAN.md

Rédei's formula is formalized: `ZInQ.RouteK.Rank5b.RedeiFormula` is proved as
`ZInQ.RouteK.Redei.redeiFormula` (`ZInQKernel/RouteK/Redei/`, the eight modules of
`docs/research/redei-plan.md` §3.2: ambiguous classes `Cl[2] = im ψ`, genus characters, their
surjectivity by Dirichlet's theorem, genus theory `Cl² = ⋂ ker χ_q` by counting, the 4-rank
statement `odd_gCl_iff`, and the 𝔽₂ linear algebra matching Rédei's matrix with the bits `gBit`).
Hence `CertifiedRankTYZCl ↔ CertifiedRankTYZ` unconditionally (`certifiedRankTYZ_iff'`), and the
main-theorem variants `..._sixContactMin_certifiedRankTYZCl` and `..._sixContactMin_certifiedRankTYZClRk`
take only SixContactMin and the Tian–Yuan–Zhang hypothesis in class-number form; the trust statement
for CR₃ in that form names only Tian–Yuan–Zhang and Gross–Zagier, not Rédei.

## Build and checks

* `lake build ZInQKernel`: succeeded (9918 jobs), no `sorry` warnings.
* `lake env lean scripts/print_axioms.lean`: all 49 entries depend only on
  `[propext, Classical.choice, Quot.sound]`, including `redeiFormula`, `oddGClStatement` and the two
  main-theorem variants without `hR`.
* No `sorry`, `axiom` or `native_decide` in `ZInQKernel/RouteK/Redei/`.

## Problems, suggestions

* KERNEL_PLAN.md still says Rédei's formula is not formalized (lines ~134–140); it was outside my
  allowed paths. The paragraph above is meant to replace that passage.
* The probe `scratch/redei-plan/Probe.lean` states `odd_gCl_iff` without `1 < n`, which makes it
  false at `n = 1`. I left the probe unchanged, since it is scratch; the Lean theorems carry the
  hypothesis. (`range_sq_eq_ker_chi` actually holds at `n = 1`, because there the class group is
  trivial, but the counting proof needs `1 < n`, so the Lean version has it.)
* The step 6 counting went through as planned (route (c)) in about 330 lines, with no new
  infrastructure.
