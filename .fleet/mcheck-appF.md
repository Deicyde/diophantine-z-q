# mcheck-appF: fleet note

**Task.** Line-by-line check of Appendix F, tex L8408-9405: ex:app-theta-form (odd theta forms, (O.3)-(O.6)) and
ex:app-theta-comparison (the unaveraged comparison (O.7)). Report: `docs/research/mcheck-appF.md`. Scripts and log:
`scratch/mcheck-appF/`.

**Result.** No error. `.fleet/mcheck-appF-verdict.md` was not written. The range holds as written, relative to the
cited prints and to standard facts about supersingular reduction.

**What the scripts check.** There are five pure-Python scripts, each with negative controls. Totals: s1 48/48, s2 20/20,
s3 27/27, s4 2/2, s5 4/4 PASS.
- **Constants and local weights:** c_0 = |GL_4(F_3)|, v2 = 9; the local weights and their signs; alpha(-1) = 1, with
  root numbers computed from L-series.
- **Characters and the double cover:** the Weil-index identities (O.5a)-(O.5c) at 2, odd p and infinity; the scalars of
  the double-cover relations; the inverse-idele convention (an order-4 character test); the extraction character (m/.).
- **Global model:** the line and neighbour counts behind (O.6), and a global weighted ternary theta model on
  B = (-1,-3). In that model (O.6) holds; every orientation contributes the same weight; the support count is
  12 h(F); and the genus cancellation for D > 1 reproduces (O.7)'s structure c_0 2^{omega(N)} with no class-number
  division.

**Gaps filled (presentation only).**
- F-a: the Brandt adjointness step at L9067-9081.
- F-b: the final (-1) in the formula for alpha(-1) is (-1/l_0).
- F-c: (O.7) holds mod 2^M O.
- F-d: zeta is fixed only up to a reference-class sign.

**Unverified.**
- Cornut-Jetchev Thm 3.1, Cor 3.2 and §§3.6, 4.9-4.10 (preprint; the hypotheses H.1-H.3 could not be read). This is
  the only input to sum chi_F P_M(z_a) = lambda_M(L P_D bar).
- Weil III Thm 6, holomorphy at the cusps, and the normal form of the double cover.
- Hecke, Atkin-Lehner and Frobenius compatibility of P_M (standard, no print cited).
- The Voight and Jetchev-Kane locators.

**Uses of (O.7).** (3.8) at L2522-2534 (the identical statement, with zero when (D/l_0) ≠ 1); phase removal at
L2081; (O.8) at L9425; D = 1 at L2588 via (O.8); (F.6) nonempty at L10194, via v2 a_M(D_w) = 9 + omega(N) + c_w. In
each case the statement proved is the statement used.

**GZ/TYZ.** None in this range. (O.7) is a reduction identity of Gross type, not a height formula. CST 1.1 enters only
next door (ex:app-detector, (O.8)).

**Next.** Read the CJ print for K1 (S = {l_0}, the sign fibre, the "integer 2" in H.2). Optionally, extend s3 to a
level-N Eichler order with nonconstant P.
