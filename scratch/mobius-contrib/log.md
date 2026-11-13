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

## Step 1b: trimmed to the dependency closure
- `Dead.lean` (Lean metaprogram) computes the constants reachable from mobiusGlue_of_T5,
  mobiusGlue_of_t5, imagePlaneCurveClosed (types, values, ctors) and lists the Mobius
  declarations outside it with their source ranges (`dead.out`): 65 dead of 284. VERIFIED.
- `trim.py` removed them (keeping any whose name occurs textually in the remaining code: only
  `GlobalFunctionsConst`, then removed by hand after a second `Dead.lean` run, `dead2.out`).
  Removed lists are in each module header. Kept text verbatim (blank-line runs collapsed).
- New `Main.lean` (imports ImagePlane; #print axioms). All five modules build in order. VERIFIED.
- Lines: InfraDim 388, Glue ~1210, CurveFacts ~1600, ImagePlane ~790 (was 4693 in one file).
- #print axioms (Main.lean, lake build): mobiusGlue_of_T5, mobiusGlue_of_t5,
  imagePlaneCurveClosed: [propext, Classical.choice, Quot.sound]. VERIFIED.
