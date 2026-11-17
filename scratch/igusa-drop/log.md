# igusa-drop results log

Base wip/leaf-fold33b 97247ce1 (top `sixContactMin_of_open71`, TailZ78). Build tree copied (reflink) from
~/dzq-wt/leaf-fold33b (same HEAD, byte-identical Main.lean).

1. Readers of `igusaGL2DSGalSome` on the live chain (VERIFIED, grep of ZInQKernel/OneProof/H/TailZ7[5-8].lean):
   TailZ78 `openResearchLeaves51_of_OpenResearchLeaves52` passes it through; TailZ77's composite
   `openResearchLeaves36EBCF_of_OpenResearchLeaves51` reads it once, in
   `r16CoreY := AfTateLam.r16CoreY_of_ds965 … (X1Igusa.igusaGL2DS_of_igusaGL2DSGalSome n.igusaGL2DSGalSome) …`;
   the result bundle `OpenResearchLeaves36EBCF` has no Igusa field. `r16CoreY_of_ds965` passes hI to
   `r16CoreY_of_printed`, which uses it only as `X1Igusa.x1PointsConjugate_of_igusaGL2DS hI` (AfTateLambda.lean:868).
2. New module ZInQKernel/Contrib/OneProof/IgusaDrop.lean (imports R16CoreYDS965 (→ AfTateLambda), RLeaf.T40,
   OneProof.ModularEquationGeneric):
   * `AfTateLam.x1PointsConjugate_proof : R16IsJ1Dict.X1PointsConjugate :=
      X1Igusa.x1PointsConjugate_iff_igusaTransitive.mpr (ZInQ.RLeaf.igusaTransitive_iff_x0Transitive.mpr FltCqj2.x0Transitive_proof)`
   * `AfTateLam.r16CoreY_of_printed_x0 (h1 : HeckeJ1DS) (h2 : AfShimura) (h3 : AfTateDSLambda) (hM : AvSplit.MumfordTorsionAlgClosed) : R16Split.R16CoreY`
     (proof of r16CoreY_of_printed verbatim, the one use of hI replaced)
   * `AfTateLam.r16CoreY_of_ds965_x0 (h1) (h2) (h3 : AfCharpolyDS965) (hM) : R16Split.R16CoreY`
   `lake build ZInQKernel.Contrib.OneProof.IgusaDrop`: Build completed successfully (12092 jobs); all three
   `#print axioms`: [propext, Classical.choice, Quot.sound] (VERIFIED). Import acyclic (new leaf module; nothing imports it).
3. Generator scratch/igusa-drop/gen_igusa_drop.py (fold-b105's gen_chev_bypass.py with FIELD = igusaGL2DSGalSome and
   the reader rule `r16CoreY_of_ds965 a b c (igusaGL2DS_of_igusaGL2DSGalSome X.igusaGL2DSGalSome) d` ->
   `r16CoreY_of_ds965_x0 a b c d`). Walk (VERIFIED, generator output): sixContactMin_of_open71:
   openResearchLeaves51_of_OpenResearchLeaves52 -> sixContactMin_of_open70 -> openResearchLeaves36EBCF_of_OpenResearchLeaves51;
   stop at OpenResearchLeaves36EBCF; readers ['r16CoreY']. OpenResearchLeaves52 (28 fields) -> OpenResearchLeaves53 (27).
   Wrote ZInQKernel/OneProof/H/TailZ79.lean (OpenResearchLeaves53, openResearchLeaves36EBCF_of_OpenResearchLeaves53,
   sixContactMin_of_open72); Main.lean switched; kinds.tsv row igusaGL2DSGalSome dropped (no claims row, no reviews row).
   render count: strict 6/24 on 30 -> 5/24 on 29 (the field was LEAF/LEAF; GLUE unchanged; -1 field).
   `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.IgusaDrop`:
   Build completed successfully (16226 jobs); 'HDec.HSyn.sixContactMin_of_open72' and 'ZInQ.OneProof.frozenTarget'
   depend on axioms: [propext, Classical.choice, Quot.sound] (VERIFIED; build log left out of the commit).
4. Checks after the fold (VERIFIED; `bash scratch/igusa-drop/run_checks.sh ~/dzq-wt/leaf-fold33b`, output run_checks.out):
   * hash guard (DumpCompact; base dump with LEAN_PATH on the base build tree of ~/dzq-wt/leaf-fold33b at 97247ce1, its
     frozenTarget type over OpenResearchLeaves52): before 18128, after 18163 constants; only before 0; only after 35 (all
     in ZInQKernel.OneProof.H.TailZ79); changed 1: ['ZInQ.OneProof.frozenTarget'] (cmp_hashes.txt; hash dumps kept out
     of the commit, 1.7 MB each).
   * #print axioms ZInQ.OneProof.frozenTarget: [propext, Classical.choice, Quot.sound].
   * FoldCheck.lean (closure of frozenTarget, 304529 constants): sorryAx, X1Igusa.IgusaGL2DSGalSome,
     igusaGL2DS_of_igusaGL2DSGalSome, X1Igusa.IgusaGL2DS, x1PointsConjugate_of_igusaGL2DS, AfTateLam.r16CoreY_of_ds965,
     AfTateLam.r16CoreY_of_printed, OpenResearchLeaves52, sixContactMin_of_open71 all absent; r16CoreY_of_ds965_x0,
     x1PointsConjugate_proof, FltCqj2.x0Transitive_proof, igusaTransitive_iff_x0Transitive, OpenResearchLeaves53,
     sixContactMin_of_open72 present. (First FoldCheck run had a copy error in the `checked` list; fixed and rerun.)
   * OpenStatements.lean: 34 open hypotheses (was 35).
   * render_open: 29 H hypotheses, strictest 5/24, 5 others (was 30, 6/24); --check: ok, 34 open, 4 generated files up
     to date. STATUS.md, OPEN.md, CONTRIBUTING.md, open-statements.json regenerated.
   * DischargesTest rerun: 19 DISCHARGES lines, no error.
   * frontier_crosswalk: 232 IDs, 4 matched; --check ok.
   * autoform check blueprint (46b46d6d): exit 0, OK: 776 articles, 2337 dependencies.
   * `#discharges` cannot show igusaGL2DSGalSome as DISCHARGED: this is a bypass (IgusaGL2DSGalSome itself is not
     proved); the closure check shows it gone, as for fold-b105's chevalleyPerfect.
   Count: 35 -> 34 open; H 6/24 on 30 -> 5/24 on 29 (-1 field, -1 LEAF; strict GLUE unchanged).
5. Replay (VERIFIED, text): generator run in a temporary worktree at 159fcd50 (Contrib commit, pre-fold) produced
   TailZ79.lean, Main.lean, kinds.tsv, claims.tsv byte-identical to the committed fold (cmp); worktree removed. On the
   folded head the generator prints "OpenResearchLeaves53 has no field igusaGL2DSGalSome: nothing to do".
6. Report docs/research/igusa-drop.md, .fleet/igusa-drop.md.
