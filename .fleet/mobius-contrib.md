# mobius-contrib (2026-11-13)

**Main result.** image-plane's proof that the kernel's `MobiusGlue` follows from the textbook leaf
T5 now builds in the Contrib tree, under `ZInQKernel/Contrib/Mobius/`. The modules are InfraDim,
Glue, CurveFacts and ImagePlane, plus Main, which imports ImagePlane. `lake build
ZInQKernel.Contrib.Mobius.Main` succeeds. `#print axioms` gives [propext, Classical.choice,
Quot.sound] for all three theorems:

```lean
theorem LeafQM.AV.CurveGlue.mobiusGlue_of_T5 (hT : ObjBridge.TorsionStructure) : MobiusGlue
theorem LeafQM.AV.CurveGlue.mobiusGlue_of_t5 (h : PkgI2.TorsionStructure.{0}) : MobiusGlue
theorem LeafQM.AV.Pin.imagePlaneCurveClosed : ImagePlaneCurveClosed
```

`MobiusGlue` is the kernel's `LeafQM.AV.Pin.MobiusGlue` (HDecomp/QM/Pin.lean). It is imported,
not redefined.

**What compiles.**
- The source was cut at its section boundaries. The 65 declarations that the three theorems do
  not depend on were removed: the (L0)/(L) routes and the CM-free forms. The dependency closure
  was computed in Lean (`scratch/mobius-contrib/Dead.lean`).
- The kept text is verbatim, with no renames and no statement changes (checked by `subseq.py`).
- `scratch/contrib-check/Check.lean` imports `Contrib.Mobius.Main` and prints the axioms of both
  `MobiusGlue` theorems. It builds with 0 errors, and every axiom set it prints is the standard
  three.

**What remains.**
- Step 3 (a closed `GluePiecesPin.mobius`) is not done, because T5 (`PkgI2.TorsionStructure`) is
  not proved in Contrib on any branch. Once it is, the closed form is `mobiusGlue_of_t5 <T5>`.
- `GluePiecesPin` and `TextbookLeaves` exist only in `scratch/h-decomposition/Leaves.lean`.
- `ImagePlaneCurveClosed` is a scratch copy: curve-glue's definition, now defined in
  `Contrib/Mobius/CurveFacts.lean`, not a kernel HDecomp definition. Its proof is in Contrib, but
  it proves that copy, not a kernel Prop.

Report: `docs/research/mobius-contrib.md`. Log: `scratch/mobius-contrib/log.md`.
