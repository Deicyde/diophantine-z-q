# lane74 (2026-11-17): Route K removed, manuscript pole polynomial, headline H + PC (fork #76-#79)

**Result.** New headline `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness
(hH : SixContactMin) (hPC : PoleCompleteness) : FrozenTarget` (MainGreenTao.lean). Final
`ZInQ.OneProof.frozenTarget (r : OpenResearchLeaves48) (t : OpenTextbookLeaves18) (l : OpenAddedLeaves27)
(hPC : ZInQ.PoleCompleteness) : ZInQ.FrozenTarget`. Both have axioms [propext, Classical.choice, Quot.sound].
h21S, hCM, h33c, hBFH, hGZss are gone. PC is now the manuscript's Theorem 5.2 for its own Q_pole (A + 3e, Az² + 3eH;
ms lines 976-982, 1001-1004). Manuscript.polePoly/PoleSoluble/PoleCompleteness are abbrevs of the ZInQ ones.
(VERIFIED, compiled)

**#77.** Tag route-k-final is local on bf691da2 (SHA from landed.txt). The push failed with 403, so the lead pushes
it (scratch/lane74/TAG.md). **Deleted 220 files, 70 475 lines.**
Importer findings, none deleted:
1. 78 named Route K/TYZ/CR3 files (27 831 lines) are imported by the H chain:
   OneProof/H/TailZ34 → Contrib/OneProof/RayClassShimura (and RingClassLattice) → TYZGenus.ShimuraModFn → ...
   → TYZDecomp, HeckeAll, HeckeFE, CR3Literature, TYZInputs, CertifiedRank, RouteK.{Slots,System,Selmer,Rank,
   Rank5b,Redei,PropN}.
2. Density/CharSum (headline path) imports RouteK/Selmer/CharSum.
3. The chain's scratch/contrib-check/Check.lean imports deleted modules. A fixed copy that compiles is
   scratch/lane74/contrib-check-Check.lean.
4. blueprint/ names 199 deleted declarations in 59 articles. `autoform check --lean-root` and
   `render --require-declarations` fail until #81.

**Compiles** (after the last Lean change): lake build ZInQKernel; +OneProof.Main +Discharges + AllContrib; every
tracked Contrib file; print_axioms (463 decls, standard; check_target ok); render_open --check ok (32 open:
31 H + hPC); autoform check blueprint ok.

**Remains.** Blueprint articles (#81); push the tag; swap the contrib-check file; cut the H chain's TYZGenus
import so the 78 kept files can go. The full chain (#80) was not run, as instructed. No on-the-spot statements.
Report: docs/research/lane74.md; log: scratch/lane74/log.md.
