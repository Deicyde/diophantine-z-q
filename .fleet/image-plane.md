# image-plane — (G1') ImagePlaneCurveClosed: PROVED (no hypotheses, no leaf)

**Result.** `scratch/image-plane/ImagePlaneFinal.lean` proves
`LeafQM.AV.Pin.imagePlaneCurveClosed : ImagePlaneCurveClosed`. The statement is curve-glue's,
copied verbatim. The same file proves `LeafQM.AV.CurveGlue.mobiusGlue_of_T5 (hT :
ObjBridge.TorsionStructure) : MobiusGlue`, using the kernel's `MobiusGlue`. There is also a variant
`mobiusGlue_of_t5` that takes `TextbookLeaves.t5` directly. The file compiles with 0 errors, and
all eleven final theorems have axioms `[propext, Classical.choice, Quot.sound]` (VERIFIED,
`run_ImagePlaneFinal.txt`).

**New proofs.** curve-glue had reduced G1' to the leaf (L0) and two glue Props, (AD) and (IC).
All three are now discharged:
- **(IC) `ImageClosed`:** proved from `IsProper` alone. The graph is cut out in `X ×_K Spec K[x][y]`
  by basic opens. Mathlib's `UniversallyClosed`/`isClosedMap` closes the image, and Jacobson gives
  `K`-points.
- **C2K `ConstOrOntoAlgClosed`:** proved from (CI) and the closed image (with `ρ = σ`, and again
  with `1/σ`), so the leaf (L0) `FiniteGlobalSections` is no longer needed.
- **(AD) `AlgDep`:** proved from C1b (infra-smooth-dim), C2K and (CI). Proper closed subsets of a
  component are finite (coheight argument), and the IC equations give a nonzero `P`.

**Effect.** Row 12 of the h-decomposition glue table (`MobiusGlue`, the field `mobius` of
`HSyn.GluePiecesPin`) now rests only on the textbook leaf T5, which is already in
`TextbookLeaves`.

**Compiles.**
- `ImageClosed.lean` (IC alone).
- `AlgDepProof.lean` (IC, AD, C2K).
- `ImagePlaneFinal.lean` (curve-glue's `MobiusFinal.lean` verbatim, plus the three new parts).

Every copied statement is identical to its source (`py/verbatim.py`: ALL OK).

**Remains.** Only integration into `ZInQKernel/`: kernel modules for this mathematics, then fill
`GluePiecesPin.mobius` with `mobiusGlue_of_t5 t.t5`. No human review yet.
Report: `docs/research/image-plane.md`; log: `scratch/image-plane/log.md`.
