# mobius-contrib results log

## Setup
- Merged origin/wip/image-plane (8f9505f7) and origin/main (b7cdba8e) into wip/mobius-contrib. VERIFIED (git).

## Step 1a: verbatim split (split.py)
- `scratch/mobius-contrib/split.py` cuts `scratch/image-plane/ImagePlaneFinal.lean` into
  `ZInQKernel/Contrib/Mobius/{InfraDim,Glue,CurveFacts,ImagePlane}.lean` (source lines 45-496,
  498-1711, 1713-3895, 3897-4681; bodies verbatim, new headers only).
- `lake build` of each module in order: all succeed (InfraDim, Glue 14 s, CurveFacts 8 s, ImagePlane 44 s). VERIFIED.
- #print axioms (in ImagePlane.lean): mobiusGlue_of_T5, mobiusGlue_of_t5, imagePlaneCurveClosed:
  [propext, Classical.choice, Quot.sound]. VERIFIED.
- No name clashes with Pin/SkolemNoether imports. VERIFIED (compiled).
