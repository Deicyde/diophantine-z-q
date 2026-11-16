# pi0-prune: `deligneComponentsX6PrintedAb` and `geomConnOfAlgClosure` removed from the single proof

Task pi0-prune, 2026-11-15/16. Base: fork main 43513d87 (leaf-fold25). Results log: `scratch/pi0-prune/log.md`.
Model work, no human review.

Marks: **VERIFIED** means compiled, or read in a named file at the base. **STANDARD** means published, with an exact
reference. **SPECULATIVE** means judgement.

## 1. Result

`ZInQ.SixContactMin` is proved from the current bundles `OpenResearchLeaves22`, `OpenTextbookLeaves11` and
`OpenGlue7`, together with `OpenAddedLeaves17` minus its two fields `deligneComponentsX6PrintedAb` and
`geomConnOfAlgClosure`. No `sorry`; standard axioms. VERIFIED: `lake build ZInQKernel.Contrib.OneProof.Pi0Prune`
succeeds.

* **Weak row.** The proof goes through the weak form `LeafAdopt.R1R2fpRepW` of the row `r1r2`: `R1R2fpRep` without
  its last conjunct `R1pi0Props X`.
* **Base witness.** It comes from González–Rotger's leaf `GonzalezRotgerX6`, which was already an input, instead of
  Deligne's π₀ with `GeomConnOfAlgClosure`.
* **Rethread.** Every consumer of the row on the single proof is copied with the weak row into new files. No existing
  constant changes, `R1R2fpRep` included.

Files:

| file | size | content |
|---|---|---|
| `ZInQKernel/Contrib/OneProof/Pi0Prune.lean` | 4 KB | contributor file: the main theorems |
| `ZInQKernel/Contrib/OneProof/Pi0Prune/Base.lean` | 33 KB | `R1R2fpRepW`, destructurers, producers, consumers that are not bundle maps |
| `ZInQKernel/Contrib/OneProof/Pi0Prune/Old.lean` | 52 KB | the six old bundle generations carrying the row, and their maps |
| `ZInQKernel/Contrib/OneProof/Pi0Prune/Upper.lean` | 32 KB | the stack `open17` … `open29` over `OpenAddedLeaves12P` … `17P` |

Imports: `Pi0Prune` → `Upper` → `Old` → `Base` → `ZInQKernel.OneProof.H.TailZ35`.

### 1.1 The main theorems (verbatim; `namespace HDec.HSyn`)

```lean
/-- **`OpenAddedLeaves17` minus the two fields** (`OpenAddedLeaves17P`, `Pi0Prune/Upper.lean`) from the current
bundle: every field except `deligneComponentsX6PrintedAb` and `geomConnOfAlgClosure` is copied. -/
theorem openAddedLeaves17P_of (l : OpenAddedLeaves17) : OpenAddedLeaves17P

theorem sixContactMin_of_open29P (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves17P)
    (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open29W r t l g

theorem sixContactMin_of_open29_pruned (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11)
    (l : OpenAddedLeaves17) (g : OpenGlue7) : ZInQ.SixContactMin :=
  sixContactMin_of_open29P r t (openAddedLeaves17P_of l) g
```

`OpenAddedLeaves17P` (Upper.lean) is `OpenAddedLeaves17` (TailZ34 L117-152) without lines 128-134, that is, without
the two fields and their docstrings. Its 12 fields are:
* `thetaRatiosAlgebraic`, `tateTwistInvariants`, `axSenTate`, `milneIsogenyQuasiInverse`, `shimuraTaniyamaQbar`,
  `egaIV_8_10_5_xii`;
* `deligneComponentsY3PrintedAb`, `picRepresentableAbVar`, `picZeroAbVar`, `phiAmpleIsogeny`, `weilPairingMumford`,
  `shimuraIntegralModelRep`.

Each field keeps its original type.

### 1.2 The weak row and its producer (verbatim; Base.lean)

```lean
namespace HDec.LeafAdopt  -- open CategoryTheory AlgebraicGeometry Limits; open LeafQM LeafQM.AV
def R1R2fpRepW : Prop :=
  ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
    (X : Over (Spec (CommRingCat.of ℚ))) (Ψ : (fieldPt Qbar ⟶ X) ≃ Quotient (pairSetoid Qbar))
    (fY : Y ⟶ X) (π₆ : ToP1 X.left),
    R1fpProps Y Φ ∧ R1heckeProps Y Φ ∧ X6Props Y Φ X Ψ fY ∧ R2X6PropsIff X Ψ π₆ ∧
      R1recProps Y Φ ∧ X6Surj Y X fY π₆ ∧ R5ptProps X Ψ
theorem R1R2fpRepW_of_rep (h : R1R2fpRep) : R1R2fpRepW
theorem R1R2fp_of_repW (h : R1R2fpRepW) : R1R2fp          -- proof of R1R2fp_of_rep unchanged

namespace HDec.QMSplit.Moduli
theorem r1r2_of_publishedW (hT : PkgI2.TorsionStructure.{0}) (hB : BabaGranathRational)
    (hR : ShimuraGlue.Ray.RayClassCM) (hG : GonzalezRotgerX6) : LeafAdopt.R1R2fpRepW :=
  r1r2fpRep_of_printed_t5W hT (babaGranathX6'_of_rational' hB) (ShimuraGlue.Ray.reciprocityCanonical_of_rayClass hR) hG
theorem x6ConicModel_of_publishedW (hT : PkgI2.TorsionStructure.{0}) (hB : BabaGranathRational)
    (hR : ShimuraGlue.Ray.RayClassCM) (hG : GonzalezRotgerX6) (hC : ElkiesEquationsX6) : X6Kummer.X6ConicModel
structure X6LeavesW : Prop where          -- X6Leaves (TailZ21 L1444) without deligneX6P, geomConn
  t5 : PkgI2.TorsionStructure.{0}
  babaGranathR : BabaGranathRational
  rayClass : ShimuraGlue.Ray.RayClassCM
  gonzalezRotger : GonzalezRotgerX6
  elkiesEq : ElkiesEquationsX6
theorem x6Rows_of_leavesW (L : X6LeavesW) : LeafAdopt.R1R2fpRepW ∧ X6Kummer.X6ConicModel
```

**`r1r2_of_publishedW`'s hypotheses.** They are exactly those of the chain's `r1r2_of_published` (TailZ21 L1429)
minus `hD` and `hE`. The witness leaf is `GonzalezRotgerX6`, which `r1r2_of_published` already takes; it is the
cheapest choice, since it already lists `R1fpProps ∧ X6Props`. On the chain, `x6Rows_of_open14W` supplies the four
hypotheses from bundle fields through the existing `_iff_ab_gl` transports, exactly as `x6Rows_of_open14` does
(TailZ23 L709; VERIFIED, compiled):
* T5 from `t.mumfordTorsionAlgClosed`;
* `babaGranathRationalAb`, `rayClassCMAb` and `gonzalezRotgerX6Ab` from `r`.

**Intermediate weak statements.** Each comes with a proved implication from the statement it weakens:
* `CoarseX6OfFineW`, with `coarseX6OfFineW_of : CoarseX6OfFine → CoarseX6OfFineW`;
* `CanonicalCoarseX6W`, with `canonicalCoarseX6W_of`;
* `GeomConnX6W`, with `geomConnX6W_of : GeomConnX6 → GeomConnX6W` and `geomConnX6W_of_gr : GonzalezRotgerX6 →
  GeomConnX6W`.

Each is the original with the conjunct `LeafAdopt.R1pi0Props X` deleted.

**The producer chain**, each with the original's proof minus the clause:
* `r1r2fpRep_ofW` and `r1r2fpRep_of'W` (TailU);
* `coarseX6OfFine_ofW`, `canonicalModelY3_of_coarseW`, `pairsLift_of_canonicalW`, `coarseCompare_of_canonicalW`;
* `r1r2fpRep_of_splitW`, `canonicalCoarseX6_ofW`, `r1r2fpRep_of_split5W` and `r1r2fpRep_of_split6W`;
* `r1r2fpRep_of_printedW` and `r1r2fpRep_of_printed_t5W`.

New statements: none. No LEAF or GLUE hypothesis is introduced. `R1R2fpRepW`, `OpenAddedLeaves17P` and the
intermediate weak Props are weakenings, each with its implication proved.

### 1.3 `#print axioms` (VERIFIED; scratch/pi0-prune/Axioms_out.txt, ClosureCheck_out.txt, FoldCheck_out.txt)

The following all print `depends on axioms: [propext, Classical.choice, Quot.sound]`:
* the row and its destructurers: `R1R2fpRepW_of_rep`, `R1R2fp_of_repW`, `HSyn.r1rec_of_repW`, `HSyn.r5fp_of_repW`,
  `pairsLift_of_repW`;
* the weakenings: `coarseX6OfFineW_of`, `canonicalCoarseX6W_of`, `geomConnX6W_of`, `geomConnX6W_of_gr`;
* the producers: `r1r2fpRep_of_printedW`, `r1r2_of_publishedW`, `x6ConicModel_of_publishedW`, `x6Rows_of_leavesW`;
* the stack: `HSyn.x6Rows_of_open14W`, `sixContactMin_of_open4W`, `_open11W`, `_open17W`, `_open29W`;
* the main theorems: `openAddedLeaves17P_of`, `sixContactMin_of_open29P`, `sixContactMin_of_open29_pruned`;
* the scratch fold checks: `frozenTarget_pruned`, `frozenTarget_P` and `frozenTarget_open30`, all with
  frozenTarget's other hypotheses unchanged.

### 1.4 Checks

* **Closure** (VERIFIED, scratch/pi0-prune/ClosureCheck.lean). The closure of `sixContactMin_of_open29_pruned` has
  217,052 constants, against 244,301 for `frozenTarget`. Neither it nor that of `sixContactMin_of_open29P` contains:
  * any projection `*.deligneComponentsX6PrintedAb` or `*.geomConnOfAlgClosure`;
  * `ShimuraGlue.DeligneComponentsX6Printed(Ab)`, `GeomConnOfAlgClosure`, `R1pi0Props` or `R1R2fpRep`;
  * `r1r2_of_published`, `sixContactMin_of_open17` or `sixContactMin_of_open29`.
* **PruneScan** (VERIFIED, scratch/pi0-prune/PruneScanPi0.lean). This is r6-nf's PruneScan (origin/wip/r6-nf
  0bc2446d), rooted at `frozenTarget_pruned`: `frozenTarget` with `sixContactMin_of_open29` replaced by
  `sixContactMin_of_open29_pruned`, statement unchanged. It ran in 2 min 13 s; output in prunescan-out.txt.
  ```
  PRUNE bundle HDec.HSyn.OpenResearchLeaves22: 29 fields, unused 0: []
  PRUNE bundle HDec.HSyn.OpenTextbookLeaves11: 12 fields, unused 0: []
  PRUNE bundle HDec.HSyn.OpenAddedLeaves17: 14 fields, unused 2: [deligneComponentsX6PrintedAb, geomConnOfAlgClosure]
  PRUNE bundle HDec.HSyn.OpenGlue7: 1 fields, unused 0: []
  PRUNE prune set: 2 entries
  ```
  The prune set (prune-set.txt) is exactly `FIELD ZInQKernel.OneProof.H.TailZ34
  HDec.HSyn.OpenAddedLeaves17.deligneComponentsX6PrintedAb` and the same line for `geomConnOfAlgClosure`.
* **Counts after the fold.** Both fields are LEAF in kinds.tsv (rows 44 and 47). The H part goes from 56 to 54
  fields, with LEAF −2. claims.tsv row 23 (`geomConnOfAlgClosure`, cloud batch 2) becomes moot: the lead is
  withdrawing it.

## 2. `#discharges` (scratch/pi0-prune/discharges.txt)

```
#discharges: 63 open hypotheses, 2129 theorems checked, 123 discharge one
```

**Pi0Prune discharges no field, as expected: it is a prune.**
* **116 spurious lines.** The `DISCHARGES` lines that name a Pi0Prune constant are all auto-generated structure
  projections of the copied bundles, e.g. `DISCHARGES [OpenAddedLeaves17.shimuraIntegralModelRep] by
  HDec.HSyn.OpenAddedLeaves17P.shimuraIntegralModelRep`. Each has `still assumes: [HDec.HSyn.OpenAddedLeaves17P]`,
  i.e. the copied bundle itself.
  * By bundle: `ResearchLeaves3W` 4, `OpenResearchLeaves2W` 5, `5W` 5, `7W` 10, `8W` 14, `9W` 15;
    `OpenAddedLeaves12P` 7, `13P`–`16P` 11 each, `17P` 12.
  * They are artifacts of the copies, not discharges.
* **7 genuine lines.** They belong to the existing contributions: GRCountX6, GapSHPair, ElkiesX6Star, R16Split,
  SGA7PersistsNF, UnipotentForward and MumfordRigidity.

## 3. The fold for the integration lead

There is **no autofold spec**: no field is discharged. What the fold needs is a reroute of the top call, then a prune.
Neither option below edits `R1R2fpRep`, any consumer or any old generation. The old chain constants
(`x6Rows_of_open14` … `sixContactMin_of_open29`, `researchLeaves9_of_open14`, the old consumers) leave the closure and
can be trimmed later.

### Option A: generation style (compiled as scratch/pi0-prune/FoldCheck.lean)

1. **New chain module**, e.g. `ZInQKernel/OneProof/H/TailZ36.lean`, which imports
   `ZInQKernel.Contrib.OneProof.Pi0Prune`. It contains, verbatim from FoldCheck.lean:
   * `structure OpenAddedLeaves18 : Prop`, which is `OpenAddedLeaves17` (TailZ34 L117-152) without L128-134 (12
     fields);
   * `theorem openAddedLeaves17P_of_OpenAddedLeaves18 (n : OpenAddedLeaves18) : OpenAddedLeaves17P`, a field-by-field
     copy;
   * the stack theorem:
     ```lean
     theorem sixContactMin_of_open30 (r : OpenResearchLeaves22) (t : OpenTextbookLeaves11) (l : OpenAddedLeaves18)
         (g : OpenGlue7) : ZInQ.SixContactMin :=
       sixContactMin_of_open29P r t (openAddedLeaves17P_of_OpenAddedLeaves18 l) g
     ```
2. **`ZInQKernel/OneProof/Main.lean`.** Import the new module. At L61 replace `(l : HDec.HSyn.OpenAddedLeaves17)` by
   `(l : HDec.HSyn.OpenAddedLeaves18)`. At L69 replace `(HDec.HSyn.sixContactMin_of_open29 r t l g)` by
   `(HDec.HSyn.sixContactMin_of_open30 r t l g)`. This is compiled as `frozenTarget_open30` (axioms standard).
3. **Docs** (lead): delete kinds.tsv rows 44 and 47, drop claims.tsv row 23, and regenerate OPEN.md.

### Option B: in place (compiled as `frozenTarget_pruned`; PruneScan output above)

1. **Main.lean.** Import `ZInQKernel.Contrib.OneProof.Pi0Prune`. At L69 replace `HDec.HSyn.sixContactMin_of_open29` by
   `HDec.HSyn.sixContactMin_of_open29_pruned`. The type is unchanged.
2. **Prune the PruneScan set.** In TailZ34, delete L128-134 (the two fields of `OpenAddedLeaves17`). Then delete the
   readers that the deletion breaks and that are now dead:
   * `openAddedLeaves16_of_OpenAddedLeaves17` and `sixContactMin_of_open28` (TailZ34 L154-173, and the `#print
     axioms` line L179);
   * `sixContactMin_of_open29` (TailZ35 L115-117, and the `#print axioms` line L123).

   `openAddedLeaves17P_of` names neither field, so it compiles unchanged (SPECULATIVE: not compiled against the
   pruned TailZ34). Nothing else on the tree names `sixContactMin_of_open28`/`29` or
   `openAddedLeaves16_of_OpenAddedLeaves17` (VERIFIED, grep: only TailZ34, TailZ35 and Main.lean).

### Coordination with r6-nf (origin/wip/r6-nf 0bc2446d, not on main)

r6-nf restates the same old generations. My copies are of the base 43513d87, i.e. **before** r6-nf.

**Old-generation definitions copied** (source → copy, all in `Pi0Prune/Old.lean` unless noted):
* **TailD**: `structure ResearchLeaves3`, `ResearchLeaves3.h5`, `G0RevIsog.reverseIsogeny_of_leaves3`,
  `G0Galois.g8_g12_of_leaves3`, `G0AssembleMod.newformLeaves_of3`, `G0AssembleMod.afterG7_of3`,
  `G0Split.hom_of_common3`, `glueOutputs_of_leaves3`, `sixContactMin_of_leavesR3`, `r1r2fpFull_of`.
* **TailE**: `structure OpenResearchLeaves2`, `researchLeaves3_of_open2`.
* **TailK**: `gluePieces_of_open4`, `sixContactMin_of_open4` (and `periodMapGlue_of_leaves4`, in Base).
* **TailN**: `structure OpenResearchLeaves5`, `researchLeaves2_of_open5` (and `heckeVertWitness_of_leaves5`, in Base).
* **TailO**: `cmDescends_of6`, `qmHauptmodul_of6`, `addedLeaves4_of_open6`, `glue4_of_open6`,
  `sixContactMin_of_open6` (and `LeafQCheck.descend_main`, `LeafQCheck.cmDescends_of`, in Base).
* **TailX**: `structure OpenResearchLeaves7`, `researchLeaves5_of_open7`, `addedLeaves6_of_open7`,
  `sixContactMin_of_open7`.
* **TailZ4**: `structure OpenResearchLeaves8`, `heightRowsNo20_of8`, `r20Lower_of8`, `researchLeaves7_of_open8`,
  `addedLeaves7_of_open8`, `sixContactMin_of_open8`.
* **TailZ9**: `structure OpenResearchLeaves9`, `researchLeaves8_of_open9`, `sixContactMin_of_open9`.
* **TailZ11**: `sixContactMin_of_open10`. **TailZ13**: `sixContactMin_of_open11`.
* **TailZ23** (Upper.lean): `x6Rows_of_open14`, `addedLeaves9_of_open14`, `ss1_ss3_of14`, `researchLeaves9_of_open14`,
  `sixContactMin_of_open17`.
* **TailZ24–TailZ35** (Upper.lean): `OpenAddedLeaves12`–`17` (as `…P`), `addedLeaves12_of_open13`,
  `openAddedLeaves1{3,4,5,6}_of_OpenAddedLeaves1{4,5,6,7}`, `sixContactMin_of_open18` … `_open29`.
* **Base.lean**: `TailC fibreQMPeriod_main_rep`; `TailI propTSAll_of_pieces3`; `TailU r1b_of, x6ConicModel_of,
  r1b_of'`; `TailZ5 r1rec_of_rep, r5fp_of_rep`; `TailZ20 pairsLift_of_rep, coarseFactor_of_rep,
  coarseFactor_of_rep', x6ConicModel_of_elkies, x6ConicModel_of_elkies_t5`.

**r6-nf's touch points inside this set:**
* the field `r6` (and `r8`) in `ResearchLeaves3` and `OpenResearchLeaves2/5/7/8/9`;
* the `r8 :=` assignments in `researchLeaves3_of_open2`, `researchLeaves2_of_open5`, `researchLeaves5_of_open7`,
  `researchLeaves7_of_open8` and `researchLeaves8_of_open9`;
* the three dropped fields of `OpenResearchLeaves9`;
* `researchLeaves9_of_open14` (new binders `h6`, `hSS`) and `sixContactMin_of_open17`–`20` (binders threaded; `open20`
  supplies them from NeronDVR);
* `ss1_ss3_of14`, deleted as a dead reader.

**Sequencing:**
* **If r6-nf folds first**, regenerate the three files on the new base. The generator copies declarations **by
  name** (`scratch/pi0-prune/tools/cfg_*_n.py`), and the copies reproduce the present files byte for byte (VERIFIED).
  The steps:
  1. Rerun `scratch/pi0-prune/Copy.lean` to get the copy set.
  2. Drop `ss1_ss3_of14` from `cfg_upper_n.py` if r6-nf deleted it.
  3. Run the three `gen.py` lines in `scratch/pi0-prune/tools/README.md`.
  4. Rebuild.

  r6-nf's changes in these declarations are then copied verbatim.
* **If pi0-prune folds first**, apply r6-nf's edits to the `…W` copies listed above (same text) instead of to the
  originals, which are then off the closure.

### Coordination with st-qbar (origin/wip/st-qbar 0de7c471)

`GapST.cm_point` destructures `hRep` as `⟨…, h5, -⟩`, so it already discards `R1pi0Props`. `stQM_of` and
`cmDescends_of` use the row only through `cm_point` and `LeafQCheck.cmDescends_of`. So st-qbar needs only conjuncts
that `R1R2fpRepW` keeps (VERIFIED, read and compiled).

The W form is `scratch/pi0-prune/STQMW.lean`. It compiles (21 s), and `GapST.stQM_of` and `GapST.cmDescends_of` both
print standard axioms. Its diff against STQM.lean:
* L1: `import ZInQKernel.OneProof.H.TailO` → `import ZInQKernel.Contrib.OneProof.Pi0Prune.Base`;
* L758, L890, L908: `(hRep : HDec.LeafAdopt.R1R2fpRep)` → `(hRep : HDec.LeafAdopt.R1R2fpRepW)`;
* L764: `…, hs, h5, -⟩ := hRep` → `…, hs, h5⟩ := hRep`;
* L912: `LeafQCheck.cmDescends_of (stQM_of …) hR (…) hRep` → `LeafQCheck.cmDescends_ofW (stQM_of …) hR (…) hRep`.

In the composed fold, `hRep` is `(x6Rows_of_open14W r t l).1` in place of `(x6Rows_of_open14 r t l).1`.

## 4. Method

1. **Scope probes.** These are Lean metaprograms over the closure of `frozenTarget`, all compiled
   (scratch/pi0-prune/):
   * `Scope.lean`: the structures carrying `R1R2fpRep`, found by fixpoint (`ResearchLeaves3`,
     `OpenResearchLeaves2/5/7/8/9`), and the 57 live constants whose type mentions them.
   * `Reach.lean`: the 23 live constants whose value reads the projections of the two fields. These form the stack
     from `x6Rows_of_open14` to `open29`.
   * `Copy.lean`: the union of the two, closed upwards. That gives 79 constants plus `frozenTarget`, with line ranges.
2. **Generation.** `scratch/pi0-prune/tools/gen.py` copies each declaration with its source file's
   namespace/section/open/`set_option`/`attribute [-instance]` skeleton, removes empty blocks, and renames:
   * the copy set's names get the suffix `W`, `OpenAddedLeaves12..17` get `P`, and `R1R2fpRep` becomes
     `R1R2fpRepW`;
   * the two fields and their assignments are deleted;
   * the stack's `X6Leaves` literal loses its two lines.

   Proof edits: three destructuring patterns lose one `-` (`r1rec_of_rep`, `r5fp_of_rep`, `pairsLift_of_rep`). The
   producers are hand-written (`tools/base_producers.lean`).
3. **Compilation.** Base, Old and Upper compiled on the first or second try (8 s, a few seconds, a few seconds). Then:
   * the closure check, the frozenTarget variants and PruneScan;
   * `#discharges` and the st-qbar W form.

   One Lean process at a time throughout.
