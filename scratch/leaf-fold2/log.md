# leaf-fold2 results log

Marks: VERIFIED (compiled / read in a file), STANDARD, SPECULATIVE, UNVERIFIED.

## Setup (2026-11-13 08:45-09:20 PST)
- Base: scratch/h-decomposition/Leaves.lean (35 850 lines, `namespace HDec`, leaf-fold) and
  scratch/g0-assemble2/parts (41 parts; written against the pre-leaf-fold Leaves.lean, VERIFIED by diff:
  g0-assemble2/Leaves.lean = h-decomposition/Leaves.lean before leaf-fold's edits).
- Layout (assemble.sh): olean/LPrefix (mk_prefix.py) -> TailA (parts/[0-9]*) -> TailB (a10-a44) ->
  TailC (a45-a95) -> TailD (z*) -> TailE (b10 AbVarBC copy, b20 fold; imports T14.Main, T28.Assemble,
  RLeaf.X1ConstantField and LF2ImagePlane = scratch/image-plane/ImagePlaneFinal.lean verbatim).
  Flat file Leaves2.lean = all of it.
- Edits to g0-assemble2's parts (mk_parts.py): `_root_.PkgI4` -> `_root_.HDec.PkgI4` (16); `open ZInQ ...`
  -> `open _root_.ZInQ ZInQ ...` (10), as leaf-fold did for Leaves.lean.
- Prefix edit (mk_prefix.py): the ten `TextbookLeaves` fields that g0-assemble2 §7 found unused
  (t1, t2, t3, t4, t16b, t20, t21, t28, t29a, t29b) are deleted from the structure and from
  `textbookLeaves_of_open`; the compile then checks that nothing uses them.
- Statement checks by structure: kernel Props over Mathlib-only definitions transfer by `exact`
  (leaf-fold's method). Props over file-defined structures (AbVar, ToP1) do not: AbVarBC is copied
  (part b10, mk_abvarbc.py); image-plane's C2K/C3K use `ToP1`, converted field by field (`toP1K`).

## Olean chain (2026-11-13 09:05-09:50 PST), VERIFIED compiled
- lake build of the imported kernel modules (incl. T14.Main, T28.Assemble, RLeaf.X1ConstantField, QM.Pin,
  Textbook.SkolemNoether): ok.
- LPrefix (Leaves.lean, ten unused TextbookLeaves fields deleted): exit 0, 0 errors, 582 s. So no
  declaration of Leaves.lean uses t1, t2, t3, t4, t16b, t20, t21, t28, t29a, t29b.
- TailA: first run 12 errors. (a) 8 "already declared": part 70's copies of resQ, Vb, tate, Intertwines,
  G10Out, toRingEquivQ, cycQ, R14Det (leaf-fold put identical copies in Leaves.lean) -> deleted
  (mk_fix_tailA.py, bodies checked identical). (b) part 77 `equivariant_of_asModule`: its `simp` calls
  leave goals with the Contrib modules in scope -> explicit rewrites (probe olean/T1.lean, 0 errors).
  Then exit 0, 0 errors, 69 s.
- TailB: `G0Galois.ConjTwistNontrivial` already declared (leaf-fold copy) -> deleted from a30
  (mk_fix_b.py). Exit 0, 0 errors, ~100 s.
- TailC (a75 replaced by mk_a75.py with kernel-field's current New.lean): errors: FS4Copy and
  RigidityHom duplicates of part 40 (deleted), six-clause R1fpProps projection `hR1.2.2.2` ->
  `hR1.2.2.2.1`, an `IsDedekindFiniteMonoid` instance timeout in a95 (`ofPlus_xi'_pow_ne_zero`,
  synthInstance.maxHeartbeats 400000). Then exit 0, 0 errors, 193-243 s.
- TailD: exit 0, 0 errors; g0-assemble2's four theorems with standard axioms over the HDec base.
- LF2ImagePlane (image-plane verbatim): 0 errors, 19 s. LF2Stalks (infra-stalks Part 1): 0 errors, 9 s.
- TailE: first run errors: b07 slice missed its closing `end ZInQ.HeightBC` (fixed: lines 2955-3301);
  `T28.igusaClebschSeparation_proved` is in root namespace `T28`; conj-twist's later commit added
  `[NumberField K]` to `ConjUniformization` (a30's copy updated, mk_fix_b.py; rest of the copied lines
  unchanged by diff). Then TailB-E recompiled: all exit 0, 0 errors, no sorry.
- TailE #print axioms: all 23 theorems `[propext, Classical.choice, Quot.sound]`, including
  HDec.HSyn.sixContactMin_of_open2, gluePieces_of_open2, and each *_proved transfer (T14a, T14b, T28,
  T36, T37, T39<-T40, C1b, C2K, C3K, MobiusGlue<-T5, MulIsogeny, KerUnitOpen, AbVarBaseChange, G9<-R10HT,
  OMaximal, EndTransport, ConjTwistNontrivial, CotangentSpanBC, UniformizationLiftAnalytic).
- Kernel Props over Mathlib-only definitions were accepted by plain term proofs (T14, T28, T36, T37,
  C1b); C2K, C3K through `toP1K` (field-by-field map of `ToP1`). VERIFIED by the compile.

## Flat file (2026-11-13 09:44-10:01 PST), VERIFIED
- `lake env lean scratch/leaf-fold2/Leaves2.lean` (81 355 lines, md5 0cfffa613c4c…): exit 0 in 999 s, 0 errors, no
  `declaration uses 'sorry'`. 278 `#print axioms` reports, all `[propext, Classical.choice, Quot.sound]`
  (counted by script). The file still declares Leaves.lean's two `opaque` placeholders (R1(b), R17), as types
  of fields of the old `ResearchLeaves`; no field of the four bundles of `sixContactMin_of_open2` mentions them
  (read in parts/b20_fold.lean). No `axiom` declaration.
- `#print axioms` output for the leaf-fold2 theorems (flat file, host paths removed):
```
'HDec.HSyn.t14a_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.t14b_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.t28_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.t36_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.t37_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.t39_of_t40' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.smoothStalkDimOne_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.constOrOntoAlgClosed_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.ratFactorAlgClosed_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.mobiusGlue_of_t5'' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.mulIsogeny_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.kerUnitOpen_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.g9AbVarBaseChange_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.g9Glue_of_deRhamComparisonHT' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.oMaximal_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.endTransport_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.conjTwistNontrivial_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.cotangentSpanBC_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.uniformizationLiftAnalytic_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.researchLeaves3_of_open2' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.textbookLeaves_of_open2' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.gluePieces_of_open2' depends on axioms: [propext, Classical.choice, Quot.sound]
'HDec.HSyn.sixContactMin_of_open2' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Extra folds (10:00-10:15 PST), VERIFIED compiled (TailE)
- product-unif §1-§3 (part b08, mk_b08.sh): `ZInQ.ProductUnif.productUnifSplits` compiles over the HDec
  objects on the first try (TailE 242 s); `productUnifSplits` removed from OpenGlue2.
- unif-dims + infra-smooth-dim (part b09, modules LF2UnifRoot, LF2SmoothDim; mk_unifdims.py): first run 23
  errors, all from Leaves.lean's duplicated `ZInQ.LeafPush2`/`ZInQ.DefFaltings` declarations in
  metrization2's transport section (`open ... ZInQ.DefFaltings ZInQ.LeafPush2`): fixed by opening only
  `ZInQ.LeafPush2 (CPts cptObj cDom cEvalAt IsUniformization UniformizationExists)` and a local
  `Coe (AbVar K) (PkgI3.AbVar K)` (field by field, = LeafAdopt.abVarEquiv). `tangentDimAtOrigin_proved`
  transfers the kernel statement through `toAbVarK : ZInQ.DefFaltings.AbVar L → _root_.PkgI3.AbVar L`.
  Then TailE: exit 0, 0 errors; 26 `#print axioms`, all standard. `productMetrizationOfProductUnif` now
  follows from `t.t35` (`productMetrizationOfProductUnif_of_t35`).
- Result: OpenGlue2 has 11 fields; total hypotheses 26 + 18 + 12 + 11 = 67.
