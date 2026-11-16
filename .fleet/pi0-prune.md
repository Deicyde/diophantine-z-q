# pi0-prune: summary

Base 43513d87 (leaf-fold25). Report: docs/research/pi0-prune.md. Log: scratch/pi0-prune/log.md.

**Proved (VERIFIED, compiled; no `sorry`; every theorem `[propext, Classical.choice, Quot.sound]`).**
`ZInQ.SixContactMin` follows from the current bundles minus `deligneComponentsX6PrintedAb` and `geomConnOfAlgClosure`:
- `HDec.HSyn.sixContactMin_of_open29P (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves17P)
  (g : OpenGlue7) : ZInQ.SixContactMin`. `OpenAddedLeaves17P` is `OpenAddedLeaves17` without the two fields.
- `HDec.HSyn.sixContactMin_of_open29_pruned`: the same, over the current `OpenAddedLeaves17`, reading neither field.
  It goes through `openAddedLeaves17P_of`.
- The weak row is `HDec.LeafAdopt.R1R2fpRepW`: `R1R2fpRep` without `R1pi0Props`.
  - `R1R2fpRepW_of_rep` proves `R1R2fpRep → R1R2fpRepW`.
  - `R1R2fp_of_repW` and the other destructurers keep the original proofs.
- `HDec.QMSplit.Moduli.r1r2_of_publishedW (hT : PkgI2.TorsionStructure.{0}) (hB : BabaGranathRational)
  (hR : ShimuraGlue.Ray.RayClassCM) (hG : GonzalezRotgerX6) : LeafAdopt.R1R2fpRepW`. This is `r1r2_of_published`
  without `hD`/`hE`; the base witness comes from González–Rotger.

Files: ZInQKernel/Contrib/OneProof/Pi0Prune.lean plus Pi0Prune/{Base,Old,Upper}.lean, 120 KB in total. They hold
the 79 consumers and 6 old bundles, copied with the weak row by scratch/pi0-prune/tools/gen.py.

**Checks.**
- The closure of the new top theorem contains neither field's projection, nor `R1pi0Props` or `R1R2fpRep`.
- PruneScan, rooted at frozenTarget rerouted through `_pruned`, finds exactly
  `OpenAddedLeaves17.{deligneComponentsX6PrintedAb, geomConnOfAlgClosure}` unused, and nothing else (0/29, 0/12,
  2/14, 0/1).
- `#discharges`: 0 real discharges, as expected for a prune. Its 116 extra lines are projections of the copied
  bundles, each assuming that bundle.

**Fold (lead).** No autofold spec: this is a reroute plus a prune.
- Option A (recommended, compiled in scratch/pi0-prune/FoldCheck.lean): a new chain module with `OpenAddedLeaves18`
  (17 minus the two fields) and `sixContactMin_of_open30`, then two edits to Main.lean (L61, L69).
- Option B: point Main.lean at `_pruned`, then delete the PruneScan set and its dead readers.

The counts go from 56 to 54 H fields, LEAF −2.

**Coordination.**
- r6-nf: my copies predate r6-nf. Every copied old-generation definition is listed in report §3. After r6-nf
  lands, regenerate by name (the configs reproduce the files byte for byte).
- st-qbar: `stQM_of` uses only kept conjuncts. Its W form (scratch/pi0-prune/STQMW.lean, a 5-line diff) compiles.

**Remains.**
- Option B's prune was not compiled against an edited TailZ34 (marked SPECULATIVE).
- The fold itself.
- Trimming the dead old-chain constants afterwards.
