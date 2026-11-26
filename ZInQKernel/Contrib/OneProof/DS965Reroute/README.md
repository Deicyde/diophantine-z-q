# ds965-reroute (work in progress)

Goal: remove the research hypothesis `dsThm965AtPrimes` (Diamond–Shurman 9.6.5, GLUE) from
`ZInQ.OneProof.frozenTarget` by routing its three uses on the live route to rows that stay live,
with no new leaf. Count 24 → 23; strict and strictest GLUE 17 → 16; LEAF unchanged.

## Where `dsThm965AtPrimes` is used (base `3df47b6b`; unchanged below `TailZ103` since `9b223968`)

`TailZ103` passes it unchanged to `TailZ102`; `TailZ101` converts it to `dsThm965Printed`
(`DS965Places.dsThm965Printed_of_atPrimes`); the field
is passed unchanged through `TailZ100`–`TailZ91` into `NOSNarrowChain.lean`, the live copy chain
under `sixContactMin_of_open83_nos`. Its only readers there:

1. `openResearchLeaves36EBCFSFU_y3x6_of_54SFU_y3x6_nos`: `r11r12 := PanDict.panBerger_of_F …
   n.dsThm965Printed … n.dsThm966Printed`. `panBerger_of_F` reads the Diamond–Shurman arguments only
   through `PanBergerSplit.coeff_mem_range` (algebraicity of `a_q(g)`).
2. `openResearchLeaves27_of_…28…_nos` (`dsThm965Weak_of_printed`) and
   `openResearchLeaves24_of_…25…_nos` (`dsThm965_of_weak`), which feed
3. `researchLeaves5_of_open7_pz_eb_u_c8_y3c_nos`: `r13 := … eigenformHT_of_kato_ds …` and
   `r14 := HodgeLF7.r14Det (r14Det_of_printed r.dsThm965 r.dsThm966)`.

`r14 : G0Galois.R14Det` is read only by `researchLeaves3_of_open2_eb_u_y3c_nos`
(`eigenformRepExists_of_r14Det`, which drops the determinant) and as the field `r14det` of the
`GaloisPiecesC8` built in `sixContactMin_of_open4_cm_u_c8_y3c_nos`; the readers of that structure
(`g8_g12_of_leaves3_hf_pz_eb_u_c8_y3c_nos`, `afterG7NC_of3_hf_pz_eb_u_c8_y3c_nos`) read only
`burnside`, `odd`, `weight`, `c8`. The determinant clause is never read.

## The glue (this directory)

* `RepExists.lean`: `DS965Reroute.eigenformRepExistsG9_of_modularHT (h : ModularHTCoeff)
  (hDS : DSThm966Printed) : ZInQ.Contrib.G9.PkgI4.EigenformRepExists` (weight `≥ 2` from
  `modularHTCoeff` through T25, weight `1` from `artinTransport_proof`),
  `eigenformRepExists_hsyn_of_g9`,
  `eigenformRepExists_of_modularHT … : HDec.HSyn.EigenformRepExists`, `eigenformHT_of_kato_mht`.
* `PanBerger.lean`: `HDec.PkgI4.PanDict.coeff_mem_range_of_rep`, `panBerger_of_F' (hP) (hB)
  (hR : EigenformRepExists) : PanBerger`, `panBerger_of_F_mht (hP) (hB) (h : ModularHTCoeff)
  (hDS : DSThm966Printed) : PanBerger`.

## The copy reroute (`Chain1`–`Chain5`, generated)

Generated from `NOSNarrowChain.lean`, `TailZ91`–`TailZ103` and `C8Chain.lean`'s `GaloisPiecesC8`
by a text-level generator in the style of `scratch/nos-narrow-fold/gen_chain.py` (taint by name from
the bundles that carry a 9.6.5 field or `R14Det`, and from `GaloisPiecesC8`; suffix `DS` for
structures, `_ds` for theorems; `set_option maxHeartbeats` lines dropped):

* 112 declarations of `NOSNarrowChain.lean` copied; the rest (`ResearchLeaves3EBU_y3cNOS` and the
  declarations over it alone) are reused unchanged.
* Bundles above the conversion that reads `modularHTCoeff` (`OpenResearchLeaves64NOS`, `63NOS`,
  `60_y3x6NOS`, `59_y3x6NOS`, `54SFU_y3x6NOS`): field `dsThm965Printed` deleted.
* Bundles below it (`36EBCFSFU_y3x6NOS` down to `7EBU_y3cNOS`): the 9.6.5 field
  (`dsThm965Printed` / `dsThm965Weak` / `dsThm965`) replaced by
  `repExists : ZInQ.Contrib.G9.PkgI4.EigenformRepExists`, filled once in
  `openResearchLeaves36EBCFSFU_y3x6_of_54SFU_y3x6_nos_ds` by
  `eigenformRepExistsG9_of_modularHT n.modularHTCoeff n.dsThm966Printed`, then passed through.
  This is a derived field, not an open hypothesis.
* Readers: `r11r12 := panBerger_of_F_mht n.panPrintedF n.bergerSurveyF n.modularHTCoeff
  n.dsThm966Printed`; `r13 := HodgeLF7.eigenformHT (eigenformHT_of_kato r.eigenformHTNew
  HodgeLF7.newformOfEigenformG9 r.repExists)`; `r14 := eigenformRepExists_hsyn_of_g9 r.repExists`.
* `OpenResearchLeaves5EBU_y3cNOSDS`, `2EBU_y3cNOSDS`: `r14 : EigenformRepExists`;
  `researchLeaves3_of_open2_…_ds`: `r14 := r.r14`.
* `GaloisPiecesC8DS` = `GaloisPiecesC8` without `r14det`; its constructor in
  `sixContactMin_of_open4_cm_u_c8_y3c_nos_ds` drops `r.r14`.
* `TailZ91`–`TailZ103` copied as `OpenResearchLeaves65DS`–`77DS` without the 9.6.5 field; new
  top `HDec.HSyn.sixContactMin_of_open96_ds (r : OpenResearchLeaves77DS) (t : OpenTextbookLeaves18)
  (l : OpenAddedLeaves28) : ZInQ.SixContactMin`.

## The fold (integrator)

`OneProof/H/TailZ104.lean`: `OpenResearchLeaves78` = `OpenResearchLeaves77` without
`dsThm965AtPrimes` (the fields of `OpenResearchLeaves77DS`), the field-by-field conversion
`openResearchLeaves77DS_of_OpenResearchLeaves78`, and
`sixContactMin_of_open97 (r : OpenResearchLeaves78) t l :=
sixContactMin_of_open96_ds (openResearchLeaves77DS_of_OpenResearchLeaves78 r) t l`; `Main.lean`:
`frozenTarget (r : HDec.HSyn.OpenResearchLeaves78) …` through `sixContactMin_of_open97`
(`FoldCheck.frozenTarget_without_ds965` is that body over `OpenResearchLeaves77DS`); the
`kinds.tsv` row of `dsThm965AtPrimes` removed; OPEN.md regenerated. No existing constant changes.
`afCharpolyDS965` (the k = 2 statement on `A_f`) is untouched.

PR #202 (the `conradAppB` discharge fold) also needs `TailZ104`. Whichever lands first takes it;
the other regenerates on top (for this reroute: re-run `gen_ds.txt` with the generations up to
the new top, so that `OpenResearchLeaves…DS` follows the new bundle).
