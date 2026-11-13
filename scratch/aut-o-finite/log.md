# aut-o-finite results log

Base 2dd83306 + merge origin/wip/mobius-glue. Target `LeafQM.AV.Pin.AutOInnerFinite`
(scratch/mobius-glue/MobiusGlue.lean lines 419-428).

## AutOFinite.lean (imports ZInQKernel.HDecomp.QM.Structures, ZInQKernel.HDecomp.Textbook.SkolemNoether)
- `lake build` of the two imports: success (1m33s). VERIFIED.
- §A target copied verbatim: `diff` of MobiusGlue.lean 419-428 vs AutOFinite.lean 32-41 empty. VERIFIED.
- §7, §8 copied from MobiusGlue.lean (lines 651-906, 923-1396; `mobiusGlue_of_normalizer` and
  everything depending on curves/T5 omitted).
- run1 (05:24, 11 s): 0 errors, linter warnings only; `#print axioms` of
  autOInnerFinite_of_normalizer, normalizerFinite, autOInnerFinite: [propext, Classical.choice,
  Quot.sound]. VERIFIED (compiled).
