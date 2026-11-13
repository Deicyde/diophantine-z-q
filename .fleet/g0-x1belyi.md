# g0-x1belyi (fleet note)

**Result: `X1BelyiOnModel` (missing piece 3 of `scratch/g0-split/Split.lean`) is proved.** The
statement is copied verbatim and not changed.

* `G0X1Belyi.x1BelyiOnModel_of_belyiX1 : BelyiX1 → X1BelyiOnModel` is pure glue. It transports the
  statement along the ring isomorphism `ℚ(X) ≅ K_N` of `IsX1Model`, using four facts:
  - a ring isomorphism of `ℚ`-algebras is `ℚ`-linear;
  - Belyi functions transport through `ValuationSubring.comap`;
  - `[ℚ(X):ℚ(t)] = [K_N:ℚ(j/1728)]` (`Algebra.finrank_eq_of_equiv_equiv`);
  - `ℚ(j/1728) = ℚ(j)` inside `K_N`, and `K_N/ℚ(j)` is finite, which gives `0 < d ≤ N²`.
* `G0X1Belyi.x1BelyiOnModel_of_leaves : TorsionStructure → GoodReductionUnramified →
  X1BelyiOnModel` combines the first theorem with x1-belyi's proof of `BelyiX1`. Its two hypotheses
  are leaves: T1 (Silverman AEC III.6.4(b)) and T2 (Serre–Tate 1968 Thm 1, Néron–Ogg–Shafarevich).
  Both theorem numbers are UNVERIFIED.

**What compiles** (VERIFIED: 0 errors, no `sorry`, axioms `[propext, Classical.choice, Quot.sound]`):

* `scratch/g0-x1belyi/X1OnModel.lean` (`build.sh`), which imports `ZInQKernel.HDecomp.ModCurves.Glue`.
* The integration check `Integ.lean`, which is g0-split's `Split.lean` plus this proof
  (`build_integ.sh`, about 3 min; not committed). It proves `HSyn.sixContactMin_of_leaves_x1`: the
  same as `sixContactMin_of_leaves`, with `X1BelyiOnModel` replaced by T1 and T2. Nine g0-split
  glue pieces remain.

**What remains:** T1 and T2 are not in `ResearchLeaves`/`TextbookLeaves`. The bundles contain
abelian-variety versions over group schemes (`t5 : PkgI2.TorsionStructure`,
`r7a : PkgI2.NeronOggShafarevich`). Deriving T1 and T2 from those needs the Weierstrass curve as
an abelian-variety group scheme, which is not in Mathlib 4.35. Until then the leaf count goes up
by two.

Report: `docs/research/g0-x1belyi.md`. Log: `scratch/g0-x1belyi/log.md`.
