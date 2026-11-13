# gz-statements (task report)

**Main result.** Statement review of the two remaining Gross–Zagier leaves,
`ZInQ.GZDecomp.FHNonvanishing` (Friedberg–Hoffstein 1995) and `ZInQ.GZDecomp.GrossZagierHeegner`
(Gross–Zagier 1986, with Gross 1984). Neither leaf is stronger than its published source, and
neither is vacuous. For FH this holds provided FH's theorem allows every level, dihedral `π` and
arbitrary local data (human check H1). Both are stated over genuine Mathlib and Tau Ceti
definitions. No statement needs a repair. The gaps are of two kinds:
- scope wider than the use: all `N`, all `f`, every `B`, every `E`;
- docstring precision.

Exact fixes are proposed in `docs/research/gz-statements.md` and not applied. Both leaves are
weakened to what the glue uses, and the weakened forms still give Theorem 1.1. All theorem
numbers from the literature are UNVERIFIED (no network).

**Compiles** (`lake build ZInQKernel.Contrib.GZStatements.{Weak,Level,Compat,Hensel}`). All 22
declarations have `#print axioms` = `[propext, Classical.choice, Quot.sound]`
(`scratch/gz-statements/out_check_axioms.txt`). Namespace `ZInQ.GZStatements`:
- Restricted leaves (defs): `FHNonvanishingCd`, `GrossZagierHeegnerCd`, `GrossZagierRankCd`.
  They are restricted to `C_d`, `d ≡ 5 mod 8`, and use `D < −4` in place of `∀ B`.
- `fhNonvanishingCd_of_fhNonvanishing`, `grossZagierHeegnerCd_of_grossZagierHeegner`,
  `grossZagierRankCd_of_grossZagierHeegnerCd`: the restricted forms are weaker.
- `grossZagierCd_of_fhNonvanishingCd_grossZagierRankCd`,
  `grossZagierCd_of_fhNonvanishingCd_grossZagierHeegnerCd`,
  `frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierHeegnerCd`,
  `frozenTarget_of_sixContactMin_tyzThm35ReadingA_fhNonvanishingCd_grossZagierRankCd`: the
  restricted forms still close the chain, using atkin-li's proved `HeckeThetaNewform`.
- `grossZagierRankCd_of_grossZagierCd`, `grossZagierHeegnerCd_of_grossZagierCd`,
  `grossZagierHeegnerCd_of_grossZagier`: the restricted GZ leaf is no stronger than the premise
  it replaces. Given L2 it is equivalent to `GrossZagierCd`.
- `level_eq_of_coeff_cd`: any newform with `aₙ = aₙ(C_d)` has level `32 d²`. Also
  `heegnerHyp_iff_of_coeff_cd` and `heegnerHyp_32_iff`.
- Checks on the definitions:
  - `heegnerHyp_iff_split`: `HeegnerHyp` is the splitting condition;
  - `exists_sq_mod_four_mul_of_heegnerHyp`: it implies GZ's `D ≡ β² mod 4N`;
  - `coprime_of_heegnerHyp`;
  - `jacobiSym_neg_level`: `χ_D(−N) = −1`, so the twists have root number `+1`, which is FH's
    compatibility hypothesis;
  - `jacobiSym_two_eq_one_iff`, `jacobiSym_prime_eq_legendreSym`, `chiD_mul`, `chiD_prime`,
    `chiD_two`: `chiD` is the Kronecker character.

**Remains.** A human must compare the leaves with the printed papers (report §6, H1-H6):
- FH's central-value theorem: generality in level, dihedral `π` and local data; its label A/B;
- the twisted root-number formula;
- GZ's standing hypotheses on `(N, D)` and the Ch. V formula;
- the sign in Gross's conjugation relation (made irrelevant by a Kolyvagin cross-check);
- Shimura's modular parametrization of CM curves.

**Proposal to the owner**: replace the premises `FHNonvanishing` and `GrossZagierHeegner` by
`FHNonvanishingCd` and `GrossZagierHeegnerCd`. The headline with them is proved. Nothing was
left unproved among this task's Lean goals.
