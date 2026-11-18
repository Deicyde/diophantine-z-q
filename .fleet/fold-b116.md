# fold-b116 (fleet note)

**Verdict: all five items are folded, built and checked. No SGA 7 statement is left anywhere in the proof.** The count
is unchanged: 30 open, H strict 5/24 on 29, strictest 5/24. Branch wip/fold-b116 = wip/leaf-fold33b d804d07d plus this
task's commits, including the merges of d2a6b and r16-shimura73 (fast-forward). Report: docs/research/fold-b116.md. Log: scratch/fold-b116/log.md. Replay:
scratch/fold-b116/REPLAY.md.

1. **inbox 83: `faltingsSemistableHeightBC`.**
   - The row is now consequence, GLUE/GLUE, with the reading desk's flag and the locator §3 p. 354.
   - The leaf docstring no longer says Faltings gives SGA 7 IX 3.3 as the reason.
   - SGA 7 IX Cor. 3.3 is no longer a separate row; its content is named inside this leaf.
2. **d2a6b.** The chain and the bypass were regenerated on the post-ss-faltings top.
   - The chain is `OneProof/H/D2A6Chain.lean`, rooted at SSFChain's `sixContactMin_of_open73_sf`.
   - TailZ85 `OpenResearchLeaves59` / `sixContactMin_of_open78`: `sga7_IX_3_5_ForwardGeom_Def34` →
     `elliotWildInertiaTrivial` (ELLIOT L817-818, GLUE).
   - The superseded Contrib chain was removed.
   - Closure: 0 constants named `*SGA7*`.
3. **r16-thm1b**, by autofold with its own spec.
   - TailZ86 `OpenResearchLeaves60` / `sixContactMin_of_open79`.
   - Out: afShimura, heckeJ1DS. In: shimuraThm1Af and bShStandardModel, both GLUE.
   - The on-the-spot pieces are labelled B1 (IsX1Gen is Shimura's standard model) and B4 (the double-coset
     dictionary).
   - The G1 Prop ShimuraTotalToComponents is absent from the closure.
4. **logp-transc**, from 707e4799, not from the branch tip, which has three later commits.
   - The two Contrib files compile with standard axioms.
   - **Not in AllContrib:** the same PkgI6.TraceContainsRamificationIdx clash as HTModel.
   - The panPrintedF and bergerSurveyF flags are narrowed. Ratings are unchanged.
5. **Docs.**
   - Rows edited: javanpeykarThm111An (now note), r9a, r9b, dsThm966Printed.
   - claims.tsv gains the hPC row. The pazuki row is dropped: no activity after 11-17 12:00. No PoincareComplement row.
   - The I3Layer.lean:879 docstring is not edited (that module is not rebuilt).

**Checks after every item** (VERIFIED):
- the build passes and frozenTarget uses only the standard axioms;
- hash guard: only frozenTarget changed, plus the new constants;
- closure, OpenStatements (30), render_open, crosswalk and both `--check` runs pass;
- DischargesTest was rerun; autoform exits 0; GATE=ok.

**Remains:**
- inbox 78 item 3 waits for #90;
- AllContrib lines for HTModel and LogPTranscendence wait for wip/contrib-clashes;
- the lead may want inbox 83's §3 p. 354 locator in the javanpeykar flag and in the other "Faltings 1983 §1"
  docstrings.
