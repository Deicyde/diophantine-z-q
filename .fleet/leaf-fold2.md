# leaf-fold2: fleet summary

**Result.** `scratch/leaf-fold2/Leaves2.lean` proves
`HDec.HSyn.sixContactMin_of_open2 (r : OpenResearchLeaves2) (t : OpenTextbookLeaves2)
(l : OpenAddedLeaves2) (g : OpenGlue2) : ZInQ.SixContactMin`.
- It has no `sorry`, and its axioms are `[propext, Classical.choice, Quot.sound]` (VERIFIED: flat
  compile, see `scratch/leaf-fold2/log.md`).
- Its hypotheses are 66 named Props, with no `opaque` placeholder:
  - 26 research-level leaves. R1(b) and R17 are now concrete, and R10 and R14 are in corrected form;
  - 18 textbook leaves;
  - 13 leaves added by the wave 26-27 reductions (9 LEAF, 4 LEAF?);
  - **9 glue Props**.
- Before, the count was 90: g0-assemble2's `GluePieces3` with leaf-fold's closures, so 24 + 26 + 18
  leaves and 22 glue. Of the 90, 68 were leaves.

**Folded.**
- Textbook leaves: T14(a′), T14(b′), T36, T37 proved; T39 follows from T40.
- AbVarBC: `MulIsogeny` (so the leaf `mulEtale` goes), `KerUnitOpen`, `AbVarBaseChange`. G9 now
  comes from the corrected R10.
- From image-plane and infra-smooth-dim: C1b, C2K and C3K, so `MobiusGlue` follows from T5 alone.
- From kernel-field: `OMaximal`, `EndTransport`.
- From conj-twist: G10 from T5, T26, T35 and `HomLinearLift`, so `ArtinTorsionSurj` and
  `ConjUniformization` go.
- From infra-stalks: `CotangentSpanBC`, `UniformizationLiftAnalytic`.
- From product-unif: `ProductUnifSplits`.
- From unif-dims and infra-smooth-dim: `ProductMetrizationOfProductUnif`, from T35.
- From inner-twist: `UnramifiedConjugates`.
- From x6-kummer: `X6KummerFibre`, from the new leaf `X6ConicModel`.
- R1(b) (`r1bFamily`) and R17 (`carayolR17`) replace the opaque placeholders.
- The ten `TextbookLeaves` fields that g0-assemble2 found unused are deleted from the structure.
  The compile confirms that none is used.

**How.**
- The base is h-decomposition's `Leaves.lean`, inside `namespace HDec`, with g0-assemble2's 41
  parts re-run inside `HDec`. That needed de-duplication against leaf-fold's copies and two proof
  repairs.
- Kernel statements over Mathlib definitions are transferred by `exact`.
- Statements over the file's own structures (`ToP1`, `AbVar`) go through field-by-field maps, or
  the proof is copied.
- Every edit is in a script; the build order is in `scratch/leaf-fold2/BUILD.md`.

**Remaining glue (9).**
- `hodgeBCInjective`, `omegaBaseChange` (height-bc);
- `periodMapGlue`, `hauptmodulUnique`, `cPtsTransport` (fibre-qm-period; period-map reduced two of
  them);
- `propTSAll` (truth SPECULATIVE);
- `conjIsogMaps`;
- `modelG3`;
- `linkedTateLocal` (truth SPECULATIVE).

The full table, with kind, source and last task for every field, is
`docs/research/leaf-fold2.md` §2.
