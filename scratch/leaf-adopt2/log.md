# leaf-adopt2 results log

## Step 1. Fold (scratch/leaf-adopt2/fold.py, one shot)
- LeafPush2.lean lines 4..`end ZInQ.LeafPush2` copied as section `LeafPush2Sec` after `end LeafAdoptSec`.
- difflib of the section against the source: 3 hunks, all docstring (header note; R3 premise bullet -> Lemma P; R3 polarization paragraph). No statement line changed.
- Opaque removed: R03_LinYang, R18_Javanpeykar, R22_Pazuki, T11_RiemannGAGA, T12_ArtinComparison. Remaining opaque: R01b_ComplexUniformization, R17_Carayol, T10_TateDuality.
- Bundles: r3, r18, r22 -> ZInQ.LeafPush2.*; t11 -> t11a, t11b; t12 removed (glue target T12_ComplexConjEigen); t35 := ZInQ.LeafPush2.UniformizationExists added.
- New glue (proved by Iff.rfl): HSyn.isComplexConj_leafPush2_iff.
- Lemma P docstring repairs: QML3, R1fp (2 places), R5fp, R5fpCount, QMLeaves, R1R2fpRep, R5fpStrong, R1 comment, R1(b), bundle fields r1r2, r1rec, r5, r5count; file header.
- Compile 1: `unknown module prefix 'ZInQ'` (upstream `lean/` package unbuilt); fixed by `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant` (OK).
- Compile 1b (245s): 2 errors, `PeriodPair.lattice1` and `PeriodPair.covolume_lattice1` already declared (the two `_root_` declarations of def-faltings Part I, present in DefFaltingsSec with identical text: diff of the 17-line blocks empty). fold.py now replaces the second copies by a comment.
- Compile 2 (250s, `lake env lean scratch/h-decomposition/Leaves.lean`): exit 0, 0 errors, one `declaration uses sorry` (HSyn.glueOutputs_of_leaves, L21525). 131 `#print axioms` lines: all `[propext, Classical.choice, Quot.sound]` except the two lines for `HSyn.sixContactMin_of_leaves` (+ sorryAx). New: 14 leaf-push2 lines + `HSyn.isComplexConj_leafPush2_iff`, all standard.
- Opaque: 3 (R01b_ComplexUniformization, R17_Carayol, T10_TateDuality). `axiom`: 0. File: 21690 lines.

## Step 2. h-decomposition.md (scratch/leaf-adopt2/docs_edit.py, one shot)
- §0 claim/counts/exact claim/changelog, §2.1 R1 R2 R5 premise (3x -> Lemma P), R3 R18 R22 Lean paragraphs, §2.2 rows T10 T11 T12(glue) T35, §2.3 counts, §3 G10 G19, §4 defs rows, §5 WP1 WP10 WP12, remaining work after leaf-adopt2, §6 R5 R7.
- Counts (VERIFIED by counting bundle fields with a regex over Leaves.lean): ResearchLeaves 26 fields (24 concrete; opaque r1an, r17), TextbookLeaves 38 (37 concrete; opaque t10). Leaves: 53 of 56 concrete (21/23 research: R2-R16, R18-R22, H5; 32/33 textbook: T1-T11, T13-T31, T33-T35) + R1 in part; placeholders R17, T10, R1(b).

## Step 3. Own check (docstring correction)
- R1(b) docstring: "part (a) is T35 + lattice computation" was too strong; now "would follow from T35 with T11a, class number one of 𝒪 and the QM lattice computation; reduction not carried out". fold.py updated; re-running fold.py on the base 01267822 reproduces Leaves.lean byte for byte (VERIFIED, diff -q).
