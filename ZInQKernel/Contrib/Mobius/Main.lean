import ZInQKernel.Contrib.Mobius.ImagePlane

/-!
# mobius-contrib: the kernel's `MobiusGlue` from the textbook leaf T5

Task mobius-contrib (2026-11-13): image-plane's proof (`scratch/image-plane/ImagePlaneFinal.lean`,
report `docs/research/image-plane.md`) moved into the Contrib build, as the modules

* `ZInQKernel.Contrib.Mobius.InfraDim` (dimension theory of smooth schemes),
* `ZInQKernel.Contrib.Mobius.Glue` (mobius-glue: `MobiusGlue` from the curve facts and T5;
  `NormalizerFinite`, `AutOInnerFinite` via the kernel's Skolem–Noether),
* `ZInQKernel.Contrib.Mobius.CurveFacts` (curve-glue: the curve facts from C1b, C2K, C3K;
  (CI) `componentIrreducible`),
* `ZInQKernel.Contrib.Mobius.ImagePlane` (image-plane: (IC), (AD), C2K, (G1') and the end
  results).

Main results (in `ImagePlane`; `MobiusGlue` is the kernel's `LeafQM.AV.Pin.MobiusGlue` of
`ZInQKernel/HDecomp/QM/Pin.lean`, `ObjBridge.TorsionStructure` and `PkgI2.TorsionStructure` are the
kernel's statements of the textbook leaf T5, `A(K̄)[n] ≅ (ℤ/n)^{2g}`):

* `LeafQM.AV.CurveGlue.mobiusGlue_of_T5 (hT : ObjBridge.TorsionStructure) : MobiusGlue`
* `LeafQM.AV.CurveGlue.mobiusGlue_of_t5 (h : PkgI2.TorsionStructure.{0}) : MobiusGlue`
* `LeafQM.AV.Pin.imagePlaneCurveClosed : ImagePlaneCurveClosed` (curve-glue's (G1'); its
  statement is defined in `CurveFacts`, copied from curve-glue's scratch file, not a definition
  of the kernel's HDecomp).
-/

#print axioms LeafQM.AV.CurveGlue.mobiusGlue_of_T5
#print axioms LeafQM.AV.CurveGlue.mobiusGlue_of_t5
#print axioms LeafQM.AV.Pin.imagePlaneCurveClosed
