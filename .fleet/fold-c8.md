# fold-c8 (fleet note)

**Verdict: the joint C8 fold is in, built and checked, and it is count-neutral as expected. H strict 5/24 on 29 →
5/24 on 29, strictest 5/24 → 5/24, 30 open before and after.** Branch wip/fold-c8 = wip/leaf-fold33b b9b85486 plus this
task's commits, including the merges of origin/wip/conrad-b3 e579047cc and PR #86's head 8050603b (both clean), so the
lead can fast-forward. Report: docs/research/fold-c8.md. Log: scratch/fold-c8/log.md. Replay: scratch/fold-c8/REPLAY.md.

- **Top.** `HDec.HSyn.sixContactMin_of_open80` (TailZ87), on `OpenResearchLeaves61`, `OpenTextbookLeaves18` and
  `OpenAddedLeaves28`.
- **Out:** picRepresentableAbVar, kleimanPicZeroProper954SiteQ, hodgeTateDecompOr. **In:** conradAppB,
  scholzeH1AbVar, t10TateDuality. All six are GLUE. poincareComplement is filled by PR #86's
  `poincareComplement_proof`, so it gets no row.
- **Route.**
  - C8 follows the manuscript: Conrad App. B (p. 32 + Prop. B.3) through `C8Conrad.g12DetPZ_of_inputs`.
  - Tate 1967 is off the route (not in the closure).
  - `hodgeTateDecompAbVar` now comes from Scholze + Milne.
  - `hodgeTateDecompOr` is filled from the new leaves in the conversion and is not read.
- **How.** One generator, `scratch/fold-c8/fold_c8.py`:
  - c8-conrad2's taint and copy generator on this top, producing `OneProof/H/C8Chain.lean` (258 constants);
  - a top section built by checked edits of the live D2A6Chain declarations;
  - TailZ87, Main.lean and kinds.tsv.
  - No existing declaration changed. claims.tsv and volatile.tsv are not touched.
- **Checks** (all VERIFIED):
  - build of Main, Discharges, C8Chain and TailZ87 ok; frozenTarget uses only the standard axioms;
  - hash guard: only frozenTarget changed, 302 new constants;
  - closure: no sorryAx and no Picard-named constant;
  - OpenStatements 30; render_open, crosswalk and both `--check` runs ok;
  - DischargesTest rerun; autoform exit 0; GATE=ok.
- **Clash check.**
  - AllContrib + PR #86 + CloudB3W17bReduced co-import cleanly.
  - ClashScan over all 6640 Contrib modules: 7 fatal clashes, all pre-existing (Different ×6, divisorSum ×1), none
    from this branch.
  - The C8 modules cannot join AllContrib because the base chain itself already clashes with it (divisorSum).
- **Manuscript check.**
  - L758-764 OK. TwistCharHTWt0 is proved and labelled on-the-spot.
  - L760-764 are supported by Conrad Prop. B.3 (the reading desk's page read; not read here).
  - L864-866 Poincaré: gap filled by PR #86.
  - lem:de-rham-descent L10939-10996 OK at the level of its citations. The pro-étale vs étale comparison and general g
    are flagged in scholzeH1AbVar.
  - No error found.
- **Remaining.**
  - Reviews of the three new rows.
  - The integrator closes PR #86 after landing.
  - deRhamVpAbVarDirect is now provable from the new leaves (a LEAF row; not removed).
  - PR #86's ResidueFieldModels takes 35 min to build.
